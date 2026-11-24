import PEqualNP.Defs.Base
import PEqualNP.Defs.Misc
import PEqualNP.Defs.CircuitLowerBounds
import PEqualNP.Defs.MetaComplexity
import PEqualNP.Defs.MetaComplexityMore
import PEqualNP.Defs.MetaComplexityMinimal
import PEqualNP.Defs.MetaComplexityLgp
import PEqualNP.Defs.ProofComplexity
import PEqualNP.Defs.ProofComplexityLin
import PEqualNP.Defs.ProofComplexityMore
import PEqualNP.Defs.ProofComplexityPC
import PEqualNP.Defs.Search
import PEqualNP.Defs.SearchQ
import PEqualNP.Defs.SearchMore
import PEqualNP.Defs.Oracle
import PEqualNP.Defs.MergeMore
import PEqualNP.Defs.CircuitMore
import PEqualNP.Defs.Pebble
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.LineDegree
import PEqualNP.Defs.CircuitMoves
import PEqualNP.Defs.LowMerge
import PEqualNP.Defs.EdgeOwnership
import PEqualNP.Defs.PencilGate
import PEqualNP.Defs.BlindGate

/-!
# The definitions root

This file only gathers the modules of the definitions root, the one part of this project a
recorded statement may speak of (`lean/README.md`). The base definitions (machines, time
bounds, P, NP, reductions) are in `Defs/Base.lean`; each program's own are in its module under
`Defs/`. A program's module may import `PEqualNP.Defs.Base` and the pinned library, never this
file, which imports them all.
-/
