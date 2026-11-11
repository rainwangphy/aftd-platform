import AFTD.Prelude
import AFTD.Kb.Physics.PathCertWord
import AFTD.Kb.Physics.PathCertEdgeCountCancel
import AFTD.Kb.Physics.PathCertSign
import AFTD.Kb.Physics.PathCertMask

/-!
# pathCertWordCountCancel

Topic: quantum_mechanics   Node: 645520a48506

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

Across a four-color word the signed sum of the seven crossing-edge counts vanishes.
-/

open scoped BigOperators in
theorem pathCertWordCountCancel (a : Fin 4) (xs : List (Fin 4)) :
    (∑ j : Fin 7, pathCertSign j * ((pathCertWord a xs j).countP id : ℤ)) = 0 := by
  induction xs generalizing a with
  | nil => simp [pathCertWord]
  | cons b bs ih =>
    simp only [pathCertWord, List.countP_cons, Nat.cast_add, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, mul_add, Finset.sum_add_distrib]
    rw [ih b]
    simpa only [id_eq, zero_add] using pathCertEdgeCountCancel a b
