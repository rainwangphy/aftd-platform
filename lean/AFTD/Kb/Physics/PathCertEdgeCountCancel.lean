import AFTD.Prelude
import AFTD.Kb.Physics.PathCertMask
import AFTD.Kb.Physics.PathCertSign

/-!
# pathCertEdgeCountCancel

Topic: quantum_mechanics   Node: 5c1d170c8f6f

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

Across a four-color path edge the signed number of the seven crossing indicators is zero.
-/

open scoped BigOperators in
theorem pathCertEdgeCountCancel (a b : Fin 4) :
    (∑ j : Fin 7, pathCertSign j * (if Nat.testBit (pathCertMask j) a.val != Nat.testBit (pathCertMask j) b.val then (1 : ℤ) else 0)) = 0 := by
  revert a b
  decide
