import RandomOrderMatching
import Lean.Util.ForEachExpr

/-! Audit every declaration owned by the project, including generated ones.
Traverse actual types and bodies, projection owners, mutual inductive
families, constructor parents, and recursor-rule right hand sides. Retain
cyclic dependencies. Do not use imported cached axiom summaries. Reverse
reachability computes each project's axiom set in this conservative dependency
graph; the count is not a claim of logically minimal assumptions.
This checks dependencies; the README separately states the formal scope. -/
open Lean Elab Command

private def expressionDependencies (e : Expr) : IO (Array Name) := do
  let names ← IO.mkRef (#[] : Array Name)
  e.forEach fun subterm => do
    match subterm with
    | .const name _ | .proj name _ _ => names.modify (·.push name)
    | _ => pure ()
  names.get

private def actualDependencies (c : ConstantInfo) : IO (Array Name) := do
  let type ← expressionDependencies c.type
  let body ← match c.value? (allowOpaque := true) with
    | some value => expressionDependencies value
    | none => pure #[]
  let mut extra := match c with
    | .inductInfo v => (v.all ++ v.ctors).toArray
    | .ctorInfo v => #[v.induct]
    | .recInfo v => v.all.toArray
    | _ => #[]
  if let .recInfo v := c then
    for rule in v.rules do
      extra := extra.push rule.ctor ++ (← expressionDependencies rule.rhs)
  return type ++ body ++ extra

set_option maxHeartbeats 0 in
run_cmd do
  let env := (← getEnv).setExporting false
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut roots : Array Name := #[]
  let mut discovered : Std.HashSet Name := {}
  for (name, _) in env.constants.toList do
    if let some owner := env.getModuleIdxFor? name then
      if (`RandomOrderMatching).isPrefixOf env.header.moduleNames[owner.toNat]! then
        roots := roots.push name
        discovered := discovered.insert name
  if roots.isEmpty then
    throwError "The project axiom audit checked no declarations"
  let mut pending := roots
  let mut reverse : Std.HashMap Name (Array Name) := {}
  let mut axioms : Array Name := #[]
  let mut checked : Nat := 0
  let mut edgeCount : Nat := 0
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    let some info := env.checked.get.find? name
      | throwError "Missing actual kernel dependency {name}"
    checked := checked + 1
    if let .axiomInfo _ := info then
      unless allowed.contains name do
        throwError "Nonstandard axiom {name} is reachable from the project"
      axioms := axioms.push name
    let mut unique : Std.HashSet Name := {}
    for dependency in ← actualDependencies info do
      unless unique.contains dependency do
        unique := unique.insert dependency
        reverse := reverse.insert dependency ((reverse[dependency]?.getD #[]).push name)
        edgeCount := edgeCount + 1
        unless discovered.contains dependency do
          discovered := discovered.insert dependency
          pending := pending.push dependency
  unless checked == discovered.size do
    throwError "The raw dependency graph was not completely traversed"
  let mut rootAxioms : Std.HashMap Name (Array Name) := {}
  for axiomName in axioms do
    let mut backward := #[axiomName]
    let mut reached : Std.HashSet Name := {}
    while !backward.isEmpty do
      let name := backward.back!
      backward := backward.pop
      unless reached.contains name do
        reached := reached.insert name
        backward := backward ++ reverse[name]?.getD #[]
    for name in roots do
      if reached.contains name then
        rootAxioms := rootAxioms.insert name ((rootAxioms[name]?.getD #[]).push axiomName)
  let mut axiomFree : Nat := 0
  for name in roots do
    let dependencies := (rootAxioms[name]?.getD #[]).qsort Name.lt
    let some owner := env.getModuleIdxFor? name
      | throwError "Project declaration has no owner: {name}"
    let moduleName := env.header.moduleNames[owner.toNat]!
    let encoded := String.intercalate "," (dependencies.toList.map Name.toString)
    logInfo m!"PROJECT_DECL|{moduleName}|{name}|{encoded}"
    if dependencies.isEmpty then
      axiomFree := axiomFree + 1
  logInfo m!"Raw dependency graph: {checked} constants; {edgeCount} edges; {axioms.size} reachable axioms."
  logInfo m!"Project axiom audit passed: {roots.size} declarations; {axiomFree} have no axioms. Only propext, Classical.choice, and Quot.sound are permitted."
