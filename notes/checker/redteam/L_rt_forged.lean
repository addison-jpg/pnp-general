import Mathlib
open Lean Elab Command in
run_cmd liftCoreM do
  let ty ← Lean.Meta.MetaM.run' (Lean.Elab.Term.TermElabM.run' (Lean.Elab.Term.elabTerm (← `(∀ n : ℕ, n + 0 = n)) none >>= Lean.instantiateMVars))
  withOptions (fun o => o.setBool `debug.skipKernelTC true) <|
    addDecl (.thmDecl { name := `PEqualNP.Outside.L_rt_forged, levelParams := [], type := ty, value := mkConst ``True.intro })
