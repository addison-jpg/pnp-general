import Lean
/-!
# The base verifier (pure Lean, no Python)

`#verify_axioms Prefix allowing a b c` goes through EVERY theorem declared in a module whose name starts
with `Prefix` (among the modules imported here), computes the axioms it depends on, and fails the build
unless they are among `propext`, `Classical.choice`, `Quot.sound`. A theorem named after `allowing` may also
depend on `sorryAx`; nothing else may. It prints the totals. This is the check that does not trust
asteroid, Python or any generated report: only `lake build`.
-/
open Lean Elab Command

namespace PEqualNP.Verify

/-- the axioms a constant depends on, memoised over the whole environment -/
partial def axiomsOf (env : Environment) (n : Name) :
    StateM (Std.HashMap Name NameSet) NameSet := do
  if let some s := (← get)[n]? then return s
  modify (·.insert n {})
  let some ci := env.find? n | return {}
  let s ← match ci with
    | .axiomInfo _ => pure (({} : NameSet).insert n)
    | _ => do
      let mut acc : NameSet := {}
      for d in ci.getUsedConstantsAsSet do
        for a in (← axiomsOf env d) do acc := acc.insert a
      pure acc
  modify (·.insert n s)
  return s

syntax (name := verifyAxioms) "#verify_axioms " ident (" allowing " ident*)? : command

@[command_elab verifyAxioms] def elabVerifyAxioms : CommandElab := fun stx => do
  let pre := stx[1].getId
  let allow : Array Name := stx[2][1].getArgs.map (·.getId)
  let env ← getEnv
  let std : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mods := env.header.moduleNames
  let mut st : Std.HashMap Name NameSet := {}
  let mut nThm := 0
  let mut nStd := 0
  let mut withSorry : Array Name := #[]
  let mut bad : Array String := #[]
  let mut modsSeen : NameSet := {}
  for (n, ci) in env.constants.map₁.toList do
    let .thmInfo _ := ci | continue
    let some idx := env.getModuleIdxFor? n | continue
    let m := mods[idx.toNat]!
    unless pre.isPrefixOf m do continue
    modsSeen := modsSeen.insert m
    let (s, st') := (axiomsOf env n).run st
    st := st'
    nThm := nThm + 1
    let extra := s.toList.filter (fun a => !std.contains a)
    if extra.isEmpty then nStd := nStd + 1
    else if extra == [``sorryAx] && allow.any (fun a => a == n || a.isSuffixOf n) then
      withSorry := withSorry.push n
    else bad := bad.push s!"{n} (module {m}): {extra}"
  logInfo m!"verify_axioms {pre}: {modsSeen.size} modules, {nThm} theorems; {nStd} on propext / Classical.choice / Quot.sound only; {withSorry.size} allowed to depend on sorryAx: {withSorry}"
  unless bad.isEmpty do
    throwError "verify_axioms {pre}: {bad.size} theorems depend on other axioms:\n{String.intercalate "\n" (bad.toList.take 40)}"

end PEqualNP.Verify
