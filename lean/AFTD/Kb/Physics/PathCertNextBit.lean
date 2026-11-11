import AFTD.Prelude
import AFTD.Kb.Physics.PathCertNext
import AFTD.Kb.Physics.PathCertTake

/-!
# pathCertNext_bit

Topic: quantum_mechanics   Node: 10ec24961752

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

Each bit of the automaton state records the corresponding greedy matching choice.
-/

open scoped BigOperators in
theorem pathCertNext_bit (a b : Fin 4) (s : Fin 128) (j : Fin 7) :
    Nat.testBit (pathCertNext a b s).val j.val = pathCertTake a b s j := by
  set_option maxHeartbeats 10000000 in
    set_option maxRecDepth 100000 in
      revert a b s j
      decide
