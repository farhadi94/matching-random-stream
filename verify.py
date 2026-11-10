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
    identity = {"manifest_sha256": sha(manifest_path),
                "toolchain_sha256": sha(ROOT / "lean-toolchain"),
                "dependency_manifest_sha256": sha(ROOT / "lake-manifest.json")}
    prior = {}
    if args.resume and report_path.exists():
        previous = json.loads(report_path.read_text())
        if previous.get("identity") == identity:
            prior = {item["module"]: item for item in previous.get("modules", [])}
    report = {"status": "RUNNING", "identity": identity, "modules": [],
              "started_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()}

    def save():
        report_path.write_text(json.dumps(report, indent=2) + "\n")

    def run(command, log):
        with log.open("w") as handle:
            return subprocess.run(command, cwd=ROOT, stdout=handle,
                                  stderr=subprocess.STDOUT).returncode

    order = manifest["topological_order"] + ["RobustMatching"]
    completed = set()
    for index, module in enumerate(order, 1):
        relative = Path(*module.split(".")).with_suffix(".lean")
        source = ROOT / relative
        source_hash = sha(source)
        imports = []
        for line in source.read_text().splitlines():
            if line.startswith("import "):
                imports += [x for x in line.split("--", 1)[0].split()[1:]
                            if x.startswith("RobustMatching.")]
        if not all(dep in completed for dep in imports):
            raise SystemExit(f"Invalid dependency order for {module}")
        target = Path(".lake/build/lib/lean") / relative.with_suffix(".olean")
        (ROOT / target).parent.mkdir(parents=True, exist_ok=True)
        old = prior.get(module)
        outputs = old.get("outputs", {}) if old else {}
        reusable = bool(old and old.get("exit_code") == 0
                        and old.get("source_sha256") == source_hash and outputs
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
                 "outputs": {str(path.relative_to(ROOT)): sha(path)
                             for path in output_files}}
        report["modules"].append(entry)
        completed.add(module)
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
