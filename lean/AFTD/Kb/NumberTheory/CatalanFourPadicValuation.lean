import AFTD.Prelude
import AFTD.Kb.NumberTheory.CatalanFourEqFourteen

/-!
# catalan_four_padic_valuation

Topic: elementary_number_theory   Node: bc63dfc857a2

Provenance: helper lemma. arXiv:2611.26953, Section 2

The 2-adic valuation of the fourth Catalan number is equal to 1.
-/

/-- The 2-adic valuation of the fourth Catalan number is 1. -/
theorem catalan_four_padic_valuation : padicValNat 2 (catalan 4) = 1 := by
  rw [catalan_four_eq_fourteen]
  have h : (14:ℕ) = 2 * 7 := by norm_num
  rw [h, padicValNat_base_mul (by norm_num) (by norm_num)]
  have h7 : padicValNat 2 7 = 0 := by
    rw [padicValNat.eq_zero_iff]
    norm_num
  rw [h7]
