import Preiss.Main
import Lean

/-! Read-only inspection of the compiled declaration environment. This file
does not add a mathematical assumption or change the theorem being audited. -/
open Lean Elab Command

set_option maxRecDepth 100000
set_option maxHeartbeats 0

run_cmd do
  let env := (← getEnv).setExporting false
  let target := ``Preiss.preiss
  let some root := env.checked.get.find? target | throwError "Missing Preiss.preiss"
  logInfo m!"AUDITED_TYPE: {root.type}"
  let cachedAxioms ← Lean.collectAxioms target
  let mut queue : Array Name := #[target]
  let mut cursor := 0
  let mut seen : NameSet := {}
  let mut rows : Array Json := #[]
  let mut missing : Array String := #[]
  let mut rawAxioms : Array String := #[]
  while cursor < queue.size do
    let name := queue[cursor]!
    cursor := cursor + 1
    unless seen.contains name do
      seen := seen.insert name
      if let some info := env.checked.get.find? name then
        let refs := info.getUsedConstantsAsSet.toArray.qsort Name.lt
        queue := queue ++ refs
        let moduleName := match env.getModuleIdxFor? name with
          | some idx => env.header.moduleNames[idx.toNat]!.toString
          | none => "<current-or-builtin>"
        let kind := match info with
          | .axiomInfo _ => "axiom"
          | .defnInfo _ => "definition"
          | .thmInfo _ => "theorem"
          | .opaqueInfo _ => "opaque"
          | .quotInfo _ => "quotient"
          | .ctorInfo _ => "constructor"
          | .recInfo _ => "recursor"
          | .inductInfo _ => "inductive"
        if kind == "axiom" then rawAxioms := rawAxioms.push name.toString
        rows := rows.push <| Json.mkObj [
          ("name", toJson name.toString), ("module", toJson moduleName),
          ("kind", toJson kind),
          ("value_available", toJson (info.hasValue (allowOpaque := true))),
          ("dependencies", toJson (refs.map Name.toString))]
      else
        missing := missing.push name.toString
  let report := Json.mkObj [
    ("root", toJson target.toString),
    ("cached_axioms", toJson (cachedAxioms.map Name.toString)),
    ("raw_axioms", toJson rawAxioms),
    ("missing_constants", toJson missing),
    ("declarations", Json.arr rows)]
  liftIO <| IO.FS.createDirAll "tmp"
  liftIO <| IO.FS.writeFile "tmp/preiss-kernel-dependencies.json" report.pretty
  logInfo m!"DEPENDENCY_AUDIT: {rows.size} declarations; {missing.size} unavailable constants; axioms {cachedAxioms}"

#print axioms Preiss.preiss
