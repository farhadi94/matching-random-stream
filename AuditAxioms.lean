import RobustMatching
import Lean.Util.CollectAxioms

/-! Check every declaration owned by the imported project modules, including
generated declarations. This checks proof dependencies, not theorem relevance
or the unformalized mathematical interfaces listed in FORMAL_COVERAGE.md. -/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut count : Nat := 0
  let mut zero : Nat := 0
  for (name, _) in env.constants.toList do
    if let some index := env.getModuleIdxFor? name then
      let moduleName := env.header.moduleNames[index.toNat]!
      if (`RobustMatching).isPrefixOf moduleName then
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Nonstandard axiom {axiomName} in {name}"
        count := count + 1
        if axioms.isEmpty then
          zero := zero + 1
  if count == 0 then
    throwError "The project axiom audit checked no declarations"
  logInfo m!"Project axiom audit passed: {count} declarations; {zero} have no axioms. Only propext, Classical.choice, and Quot.sound are permitted."
