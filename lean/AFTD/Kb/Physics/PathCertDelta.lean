import AFTD.Prelude
import AFTD.Kb.Physics.PathCertTake
import AFTD.Kb.Physics.PathCertSign

/-!
# pathCertDelta

Topic: quantum_mechanics   Node: 0f0acad44fb9

Provenance: helper lemma. Finite-state path cut-matching certificate for OP-827; exhaustive transition check in experiment 22529.

The signed change of the seven greedy matching counts for one appended vertex.
-/

open scoped BigOperators in
def pathCertDelta (a b : Fin 4) (s : Fin 128) : ℤ :=
  ∑ j : Fin 7, if pathCertTake a b s j then pathCertSign j else 0
