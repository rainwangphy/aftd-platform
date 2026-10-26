import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOpt

/-!
# nonclairvoyant_scheduling_offline_opt_zero

Topic: online_algorithms   Node: 4d5af961a8c5

Provenance: helper lemma. arXiv:2610.29037 Section 4

For any natural number n, the offline optimal total completion time of the all-zero job processing vector (fun (_ : Fin n) => (0 : ℝ)) is equal to zero.
-/

/-- The offline optimal total completion time of the all-zero processing times vector is zero. -/
theorem nonclairvoyant_scheduling_offline_opt_zero (n : ℕ) :
    nonclairvoyant_scheduling_offline_opt (fun (_ : Fin n) => (0 : ℝ)) = 0 := by
  unfold nonclairvoyant_scheduling_offline_opt
  simp only [mul_zero, Finset.sum_const_zero]
  exact Finset.inf'_const _ 0
