import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordLtOneOfLeOneSubInv
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastOneLtOfTwoLe
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordNatCastPosOfTwoLe
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordOneSubPosOfLtOne

/-!
# ErrorCorrectingCodes.Codeword.qary_entropy_pos

Topic: information   Node: 1833deecae7e

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.qary_entropy_pos`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Entropy.lean (Apache-2.0); 1 verbatim; compiled here.

Positivity of the $q$-ary entropy. Let $\alpha$ be a finite alphabet with $q = \abs{\alpha}$ symbols, and let $p$ be a real
number with $0 < p \le 1 - 1/q$. Then the $q$-ary entropy of $p$ is strictly positive:
\[
H_q(p) \;=\; p\log_q(q-1) - p\log_q p - (1-p)\log_q(1-p) \;>\; 0.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
variable {x : ℝ} in
/-- The q-ary entropy `H_q(p)` is strictly positive for `0 < p ≤ 1 - 1/q`. -/
theorem ErrorCorrectingCodes.Codeword.qary_entropy_pos (q : ℕ) (p : ℝ) (hq : q = (Fintype.card α))
    (hp : 0 < p ∧ p ≤ 1 - 1 / (q : ℝ)) :
    0 < p * Real.logb (q : ℝ) ((q : ℝ) - 1) - p * Real.logb (q : ℝ) p -
        (1 - p) * Real.logb (q : ℝ) (1 - p) := by
  have hq_two : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_iff.mpr (by simpa using Fintype.one_lt_card)
  have hq_1 : (1 : ℝ) < (q : ℝ) := natCast_one_lt_of_two_le hq_two
  have hqpos : (0 : ℝ) < (q : ℝ) := natCast_pos_of_two_le hq_two
  have hp_1 : p < 1 := lt_one_of_le_one_sub_inv hqpos hp.2
  have h1p_0 : 0 < 1 - p := one_sub_pos_of_lt_one hp_1
  have h1p_1 : 1 - p < 1 := by linarith
  have hlogq_pos : 0 < Real.log (q : ℝ) := Real.log_pos hq_1

  suffices 0 < p * Real.log ((q : ℝ) - 1) - p * Real.log p - (1 - p) * Real.log (1 - p) by
    have := (div_pos_iff.mpr (Or.inl ⟨this, hlogq_pos⟩))
    simp only [Real.logb, div_eq_mul_inv]
    simp only [div_eq_mul_inv] at this
    have hdistrib : (p * Real.log (↑q - 1) - p * Real.log p - (1 - p) * Real.log (1 - p)) * (Real.log ↑q)⁻¹ = p * (Real.log (↑q - 1) * (Real.log ↑q)⁻¹) - p * (Real.log p * (Real.log ↑q)⁻¹) - (1 - p) * (Real.log (1 - p) * (Real.log ↑q)⁻¹) := by
      simp only [sub_eq_add_neg]
      rw [distrib_three_right]
      simp [mul_assoc]
    rw [hdistrib] at this
    exact this

  have h_ent_pos :
      0 < - p * Real.log p - (1 - p) * Real.log (1 - p) := by
    have hp_neg : 0 < -p * Real.log p := by
      have := mul_neg_of_pos_of_neg hp.1 (Real.log_neg hp.1 hp_1)
      simpa [neg_mul, neg_neg] using this
    have h1p_neg : 0 < -(1 - p) * Real.log (1 - p) := by
      have := mul_neg_of_pos_of_neg h1p_0 (Real.log_neg h1p_0 h1p_1)
      linarith
    linarith

  have hlog_q_sub_one_nonneg : 0 ≤ Real.log ((q : ℝ) - 1) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ (q : ℝ) - 1 := by
      have hq_two_real : (2 : ℝ) ≤ q := by exact_mod_cast hq_two
      linarith
    exact this
  have : 0 < p * Real.log ((q : ℝ) - 1)
                + (- p * Real.log p - (1 - p) * Real.log (1 - p)) := by
    exact add_pos_of_nonneg_of_pos
      (mul_nonneg (le_of_lt hp.1) hlog_q_sub_one_nonneg) h_ent_pos
  ring_nf at this ⊢
  exact this
