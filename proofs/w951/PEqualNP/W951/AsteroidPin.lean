import Mathlib
import PEqualNP.W951.AsteroidCheap
import PEqualNP.W951.Final

/-! # Pinning the copied statement

`SearchCheck.LMeta951Stmt` (AsteroidCheap) is a verbatim copy of the type of `PEqualNP.Outside.L_meta_951`.
This file checks, by the type checker, that the two are the same proposition, so the copy cannot drift.
The theorem depends on the open statement through `L_meta_951`, hence it is on the allow-list of
`Verify/All.lean`. -/

namespace SearchCheck

theorem lMeta951Stmt_of_L_meta_951 : LMeta951Stmt := PEqualNP.Outside.L_meta_951

end SearchCheck
