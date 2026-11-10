#!/usr/bin/env python3
"""Sequential Lean verification of the source manifest; no dependency updates.

Run `lake exe cache get` first. By default every local module is rebuilt.
--resume reuses only source/dependency/output hashes from this script's
previous successful module checks. The final axiom audit always runs.
"""

import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys


ROOT = Path(__file__).resolve().parent


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--resume", action="store_true")
    args = parser.parse_args()
    lake = shutil.which("lake")
    if lake is None:
        raise SystemExit("lake is not on PATH; install the pinned toolchain with elan")
    manifest_path = ROOT / "SOURCE_MANIFEST.json"
    manifest = json.loads(manifest_path.read_text())
    for name, expected in manifest["sha256"].items():
        path = ROOT / name
        if not path.is_file() or sha(path) != expected:
            raise SystemExit(f"Source manifest mismatch: {name}")
    out = ROOT / "verification"
    out.mkdir(exist_ok=True)
    report_path = out / "build.json"
    # Hash the actual compiler and every external proof artifact in LEAN_PATH.
    # Local project outputs are checked per module, not included in this identity.
    version = subprocess.check_output([lake, "env", "lean", "--version"], cwd=ROOT, text=True)
    lean_prefix = subprocess.check_output([lake, "env", "lean", "--print-prefix"], cwd=ROOT, text=True).strip()
    search_path = subprocess.check_output([lake, "env", "printenv", "LEAN_PATH"], cwd=ROOT, text=True).strip()
    external = {}
    local_build = (ROOT / ".lake/build/lib/lean").resolve()
    # `lake env` runs in ROOT, even when this script is invoked elsewhere.
    # Include core/Std explicitly: it need not occur in LEAN_PATH.
    roots = search_path.split(os.pathsep) + [str(Path(lean_prefix) / "lib/lean")]
    for raw in roots:
        if not raw:
            continue
        candidate = Path(raw)
        path = (candidate if candidate.is_absolute() else ROOT / candidate).resolve()
        if str(path) in external:
            continue
        if path == local_build:
            continue
        files = {str(f.relative_to(path)): sha(f) for f in sorted(path.rglob("*"))
                 if f.is_file() and (".olean" in f.name or f.suffix == ".ilean")}
        external[str(path)] = files
    environment = {"lean_version": version, "compiler_sha256": sha(Path(lean_prefix) / "bin/lean"),
                   "lake_sha256": sha(Path(lean_prefix) / "bin/lake"),
                   "external_artifacts": external}
    environment_hash = hashlib.sha256(json.dumps(environment, sort_keys=True).encode()).hexdigest()
    identity = {"environment_sha256": environment_hash, "manifest_sha256": sha(manifest_path),
                "toolchain_sha256": sha(ROOT / "lean-toolchain"),
                "dependency_manifest_sha256": sha(ROOT / "lake-manifest.json")}
    prior = {}
    if args.resume and report_path.exists():
        try:
            previous = json.loads(report_path.read_text())
        except (json.JSONDecodeError, OSError):
            previous = {}
            print("Invalid checkpoint; rebuilding all project modules", file=sys.stderr)
        if previous.get("identity") == identity:
            prior = {item["module"]: item for item in previous.get("modules", [])}
    report = {"status": "RUNNING", "identity": identity, "modules": [],
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}

    def save():
        temporary = report_path.with_suffix(".json.tmp")
        temporary.write_text(json.dumps(report, indent=2) + "\n")
        temporary.replace(report_path)

    def run(command, log):
        with log.open("w") as handle:
            return subprocess.run(command, cwd=ROOT, stdout=handle,
                                  stderr=subprocess.STDOUT).returncode

    order = manifest["topological_order"] + ["RandomOrderMatching"]
    completed = set()
    completed_outputs = {}
    for index, module in enumerate(order, 1):
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = ROOT / relative
        source_hash = sha(source)
        imports = []
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                imports += [x for x in line.split("--", 1)[0].split()[1:]
                            if x.startswith("RandomOrderMatching.")]
        if not all(dep in completed for dep in imports):
            raise SystemExit(f"Invalid dependency order for {module}")
        target = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (ROOT / target).parent.mkdir(parents=True, exist_ok=True)
        dependency_outputs = {dep: completed_outputs[dep] for dep in imports}
        old = prior.get(module)
        outputs = old.get("outputs", {}) if old else {}
        reusable = bool(old and old.get("exit_code") == 0
                        and old.get("source_sha256") == source_hash and outputs
                        and old.get("dependency_outputs") == dependency_outputs
                        and all((ROOT / path).is_file() and sha(ROOT / path) == value
                                for path, value in outputs.items()))
        log = out / (module + ".log")
        result = 0 if reusable else run([lake, "env", "lean", "-j1", "-o",
                                         str(target), str(relative)], log)
        unchanged = sha(source) == source_hash
        if result or not unchanged:
            report["status"] = "FAIL"
            report["failed_module"] = module
            save()
            raise SystemExit(f"Verification failed: {module}; see {log}")
        output_files = [ROOT / target]
        output_files += [Path(str(ROOT / target) + suffix)
                         for suffix in (".private", ".server")
                         if Path(str(ROOT / target) + suffix).is_file()]
        if not output_files[0].is_file():
            raise SystemExit(f"Compiler produced no object for {module}")
        entry = {"module": module, "source_sha256": source_hash,
                 "exit_code": result, "reused": reusable,
                 "dependency_outputs": dependency_outputs,
                 "outputs": {str(path.relative_to(ROOT)): sha(path)
                             for path in output_files}}
        report["modules"].append(entry)
        completed.add(module)
        completed_outputs[module] = entry["outputs"]
        save()
        print(f"{index}/{len(order)} {'REUSE' if reusable else 'PASS'} {module}", flush=True)
    result = run([lake, "env", "lean", "-j1", "AuditAxioms.lean"], out / "axioms.log")
    report["axiom_audit_exit_code"] = result
    report["axiom_audit_log_sha256"] = sha(out / "axioms.log")
    changes = [name for name, value in manifest["sha256"].items()
               if not (ROOT / name).is_file() or sha(ROOT / name) != value]
    report["source_changes_during_check"] = changes
    report["status"] = "PASS" if result == 0 and not changes else "FAIL"
    report["completed_utc"] = datetime.datetime.now(datetime.timezone.utc).isoformat()
    save()
    print(report["status"] + ": see verification/build.json and verification/axioms.log")
    return 0 if report["status"] == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
