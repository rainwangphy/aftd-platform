import AFTD.Prelude
import AFTD.Kb.Physics.PathCertRun
import AFTD.Kb.Physics.PathCertSign
import AFTD.Kb.Physics.PathGreedyRun
import AFTD.Kb.Physics.PathCertWord
import AFTD.Kb.Physics.PathCertNextBit
import AFTD.Kb.Physics.PathCertTake
import AFTD.Kb.Physics.PathCertNext
import AFTD.Kb.Physics.PathCertDelta
import AFTD.Kb.Physics.PathCertMask

/-!
# pathCertRun_eq_greedy

Topic: quantum_mechanics   Node: 52e111e10553

Provenance: helper lemma. Four-color word certificate for path cut-rank inequalities, using the transition table of experiment 22529.

The automaton output equals the signed sum of seven greedy edge counts.
-/

open scoped BigOperators in
theorem pathCertRun_eq_greedy (a : Fin 4) (s : Fin 128) (xs : List (Fin 4)) :
    (pathCertRun a s xs).2.2 = ∑ j : Fin 7, pathCertSign j * (pathGreedyRun (Nat.testBit s.val j.val) (pathCertWord a xs j) : ℤ) := by
  set_option maxHeartbeats 5000000 in
    induction xs generalizing a s with
    | nil => simp [pathCertRun, pathCertWord, pathGreedyRun]
    | cons b bs ih =>
      change pathCertDelta a b s + (pathCertRun b (pathCertNext a b s) bs).2.2 = _
      rw [ih]
      simp only [pathCertDelta, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      simp only [pathCertWord, pathGreedyRun, pathCertNext_bit, Nat.cast_add]
      simp only [Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
      change (if pathCertTake a b s j then pathCertSign j else 0) + pathCertSign j * (pathGreedyRun (pathCertTake a b s j) (pathCertWord b bs j) : ℤ) = pathCertSign j * ((if pathCertTake a b s j then (1 : ℤ) else 0) + (pathGreedyRun (pathCertTake a b s j) (pathCertWord b bs j) : ℤ))
      split_ifs <;> ring
