import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingTermU
import AFTD.Kb.Tcs.NonclairvoyantSchedulingTermL

/-!
# nonclairvoyant_scheduling_term_U_one_eq_term_L_one

Topic: online_algorithms   Node: fbc50b7a51d7

Provenance: helper lemma. arXiv:2610.29037, Appendix C.2, Proof of Theorem 4.6 (Step 6)

For every natural number n ≥ 1 and every real parameter t, the upper bound sequence term nonclairvoyant_scheduling_term_U n t 1 at index 1 is identically equal to the lower bound sequence term nonclairvoyant_scheduling_term_L n t 1 at index 1.
-/

/-- At index s = 1, the upper bound term U_1(t) coincides with the lower bound term L_1(t). -/
theorem nonclairvoyant_scheduling_term_U_one_eq_term_L_one (n : ℕ) (t : ℝ) (hn : 1 ≤ n) :
    nonclairvoyant_scheduling_term_U n t 1 = nonclairvoyant_scheduling_term_L n t 1 := by
  unfold nonclairvoyant_scheduling_term_U nonclairvoyant_scheduling_term_L
  push_cast
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have h_denom_sub : (n : ℝ) - 1 + 1 = (n : ℝ) := by ring
  rw [h_denom_sub]
  have h_cancel : t * ↑n * (↑n - 1) * (↑n + 1 + 1) / ↑n = t * (↑n - 1) * (↑n + 1 + 1) := by
    have h : t * ↑n * (↑n - 1) * (↑n + 1 + 1) = (t * (↑n - 1) * (↑n + 1 + 1)) * ↑n := by ring
    rw [h]
    exact mul_div_cancel_right₀ _ hn0
  rw [h_cancel]
  congr 1
  · ring
  · ring
