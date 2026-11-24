import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_2178_eisenstein_inner_product_classification

Topic: combinatorics   Node: 679be4a5e874

Provenance: formalization of a published result. Source: arXiv:2611.27591 Lemma 9

If an Eisenstein element u in 2 + 3ℤ[ω] satisfies |u|² ≤ 4, then u = -1 or u = 2.
-/

/-- Classification of elements in 2 + 3ℤ[ω] of norm squared at most 4 (arXiv:2611.27591 Lemma 9). -/
theorem op_2178_eisenstein_inner_product_classification (a b : ℤ) :
    let ω : ℂ := (-1 + (Real.sqrt 3 : ℂ) * Complex.I) / 2
    let u : ℂ := 2 + 3 * ((a : ℂ) + (b : ℂ) * ω)
    Complex.normSq u ≤ 4 → u = -1 ∨ u = 2 := by
  intro ω u hu
  have h3 : (0 : ℝ) ≤ 3 := by norm_num
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt h3
  have h_re_im : u.re = 2 + 3 * a - (3 : ℝ) * b / 2 ∧ u.im = 3 * b * Real.sqrt 3 / 2 := by
    dsimp [u, ω]; simp; constructor <;> ring
  have h_normSq : Complex.normSq u =
      4 + 12 * (a : ℝ) - 6 * (b : ℝ) + 9 * ((a : ℝ)^2 - (a : ℝ) * (b : ℝ) + (b : ℝ)^2) := by
    rw [Complex.normSq_apply, h_re_im.1, h_re_im.2]
    linear_combination (9 * (b : ℝ)^2 / 4) * hsq
  have h_id_real : ((3 * (2 * a - b) + 4)^2 + 27 * b^2 - 16 : ℝ) =
      4 * (Complex.normSq u - 4) := by
    rw [h_normSq]
    ring
  have h_le_real : ((3 * (2 * a - b) + 4)^2 + 27 * b^2 - 16 : ℝ) ≤ 0 := by
    rw [h_id_real]
    linarith
  have h_le_16 : (3 * (2 * a - b) + 4)^2 + 27 * b^2 ≤ 16 := by
    have h_le_int : (3 * (2 * a - b) + 4)^2 + 27 * b^2 - 16 ≤ 0 := by
      exact_mod_cast h_le_real
    linarith
  have hb : b = 0 := by nlinarith
  subst hb
  have ha : -4 ≤ 6 * a + 4 ∧ 6 * a + 4 ≤ 4 := by
    constructor <;> nlinarith
  rcases (by omega : a = -1 ∨ a = 0) with rfl | rfl
  · left
    dsimp [u]
    ring
  · right
    dsimp [u]
    ring
