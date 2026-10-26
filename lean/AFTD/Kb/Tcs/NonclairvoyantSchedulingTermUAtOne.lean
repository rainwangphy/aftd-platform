import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingTermU

/-!
# nonclairvoyant_scheduling_term_U_at_one

Topic: online_algorithms   Node: bbe76c153eba

Provenance: helper lemma. arXiv:2610.29037, Appendix C.2, Proof of Theorem 4.6 (Step 1)

For every natural number n ≥ 1 and every natural number i, the sequence term nonclairvoyant_scheduling_term_U n 1 i evaluated at parameter t = 1 equals 2 * (n : ℝ) / ((n : ℝ) + 1).
-/

/-- At parameter t = 1, the upper bound sequence term U_i(1) equals 2n/(n+1) for all i. -/
theorem nonclairvoyant_scheduling_term_U_at_one (n : ℕ) (i : ℕ) (hn : 1 ≤ n) :
    nonclairvoyant_scheduling_term_U n 1 i = 2 * (n : ℝ) / ((n : ℝ) + 1) := by
  dsimp [nonclairvoyant_scheduling_term_U]
  simp
  have : (n : ℝ) ≠ 0 := by positivity
  field_simp
