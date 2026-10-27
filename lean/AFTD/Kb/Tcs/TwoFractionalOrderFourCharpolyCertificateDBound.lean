import AFTD.Prelude
import AFTD.Kb.Tcs.TwoFractionalOrderFourRowBoundaryEntry
import AFTD.Kb.Tcs.IsStandardizedLaplacianTwoFractional
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# two_fractional_order_four_charpoly_certificate_D_bound

Topic: graphs   Node: 541354e6775e

Provenance: helper lemma. step towards standardized_laplacian_order_four_two_fractional_im_le

For an order-4 two-fractional standardized Laplacian L, the characteristic-polynomial coefficients c2, c3 satisfy c3^2 - 3 c2 ≥ -11/16.
-/

private lemma two_fractional_order_four_charpoly_certificate_D_bound_det_two_card_two
    {α : Type*} [Fintype α] [DecidableEq α] (A : Matrix α α ℝ)
    (a b : α) (hab : a ≠ b) (huniv : (Finset.univ : Finset α) = {a, b}) :
    A.det = A a a * A b b - A a b * A b a := by
  have hcard : Fintype.card α = 2 := by
    rw [← Finset.card_univ, huniv, Finset.card_pair hab]
  let e : α ≃ Fin 2 := Fintype.equivFinOfCardEq hcard
  have hA : A = (A.submatrix e.symm e.symm).submatrix e e := by ext i j; simp
  rw [hA, Matrix.det_submatrix_equiv_self e, Matrix.det_fin_two]
  have h01 : e.symm 0 ≠ e.symm 1 := by
    intro h; exact (by decide : (0:Fin 2) ≠ 1) (e.symm.injective h)
  have key : ∀ x : Fin 2, e.symm x = a ∨ e.symm x = b := by
    intro x
    have hx : e.symm x ∈ ({a, b} : Finset α) := by rw [← huniv]; exact Finset.mem_univ _
    rcases Finset.mem_insert.mp hx with h | h
    · exact Or.inl h
    · exact Or.inr (Finset.mem_singleton.mp h)
  rcases key 0 with h0 | h0 <;> rcases key 1 with h1 | h1
  · exact absurd (h0.trans h1.symm) h01
  · simp only [Matrix.submatrix_apply, h0, h1, Equiv.symm_apply_apply]
  · simp only [Matrix.submatrix_apply, h0, h1, Equiv.symm_apply_apply]; ring
  · exact absurd (h0.trans h1.symm) h01

private lemma two_fractional_order_four_charpoly_certificate_D_bound_det_pp
    (L : Matrix (Fin 4) (Fin 4) ℝ) (i j : Fin 4) (hij : i ≠ j) :
    (L.submatrix (Subtype.val : ({i,j} : Finset (Fin 4)) → Fin 4)
        (Subtype.val : ({i,j} : Finset (Fin 4)) → Fin 4)).det
      = L i i * L j j - L i j * L j i := by
  refine two_fractional_order_four_charpoly_certificate_D_bound_det_two_card_two
    (α := ({i,j} : Finset (Fin 4))) _ ⟨i, by simp⟩ ⟨j, by simp⟩ ?_ ?_
  · intro h; exact hij (congrArg Subtype.val h)
  · apply (Finset.eq_univ_of_forall ?_).symm
    intro x
    have hx : (x : Fin 4) = i ∨ (x : Fin 4) = j := by
      rcases Finset.mem_insert.mp x.2 with h | h
      · exact Or.inl h
      · exact Or.inr (Finset.mem_singleton.mp h)
    have hmem : x ∈ ({⟨i, by simp⟩, ⟨j, by simp⟩} : Finset ({i,j} : Finset (Fin 4))) := by
      rcases hx with h | h
      · rw [Finset.mem_insert]; left; exact Subtype.ext h
      · rw [Finset.mem_insert]; right; rw [Finset.mem_singleton]; exact Subtype.ext h
    simpa using hmem

private lemma two_fractional_order_four_charpoly_certificate_D_bound_sum_powerset_two
    (f : Finset (Fin 4) → ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2, f s)
      = f {0,1} + f {0,2} + f {0,3} + f {1,2} + f {1,3} + f {2,3} := by
  have hp : (Finset.univ : Finset (Fin 4)).powersetCard 2 =
      ({({0,1} : Finset (Fin 4)), {0,2}, {0,3}, {1,2}, {1,3}, {2,3}} :
        Finset (Finset (Fin 4))) := by decide
  rw [hp]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  ring

private lemma two_fractional_order_four_charpoly_certificate_D_bound_coeff_two
    (L : Matrix (Fin 4) (Fin 4) ℝ) :
    L.charpoly.coeff 2 = (L.trace ^ 2 - (L * L).trace) / 2 := by
  have h := Matrix.charpoly_coeff_eq_sum_minors (M := L) 2 (by norm_num : 2 ≤ Fintype.card (Fin 4))
  simp only [Fintype.card_fin] at h
  rw [show (4 - 2 : ℕ) = 2 from rfl] at h
  rw [h]
  have hp2 : (∑ s ∈ (Finset.univ : Finset (Fin 4)).powersetCard 2,
      (L.submatrix (Subtype.val : s → Fin 4) (Subtype.val : s → Fin 4)).det) =
      ((L.trace ^ 2 - (L * L).trace) / 2) := by
    rw [two_fractional_order_four_charpoly_certificate_D_bound_sum_powerset_two]
    rw [two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 0 1 (by decide),
      two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 0 2 (by decide),
      two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 0 3 (by decide),
      two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 1 2 (by decide),
      two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 1 3 (by decide),
      two_fractional_order_four_charpoly_certificate_D_bound_det_pp L 2 3 (by decide)]
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  rw [hp2]; norm_num

private lemma two_fractional_order_four_charpoly_certificate_D_bound_numeric
    (b0 b1 b2 b3 P : ℝ) (hb0 : 0 ≤ b0) (hb1 : 0 ≤ b1) (hb2 : 0 ≤ b2) (hb3 : 0 ≤ b3)
    (hP0 : 0 ≤ P) (hP16 : 4 * (b0 + b1 + b2 + b3) - 6 ≤ 16 * P)
    (hTle : b0 + b1 + b2 + b3 ≤ 3) :
    -(11 / 16 : ℝ) ≤
      (3 * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 + 2 * P) - (b0 + b1 + b2 + b3) ^ 2) / 2 := by
  have hsq : (b0 + b1 + b2 + b3) ^ 2 ≤ 4 * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2) := by
    nlinarith [sq_nonneg (b0 - b1), sq_nonneg (b0 - b2), sq_nonneg (b0 - b3),
      sq_nonneg (b1 - b2), sq_nonneg (b1 - b3), sq_nonneg (b2 - b3)]
  have hTn : 0 ≤ b0 + b1 + b2 + b3 := by linarith
  rw [show (3 * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2 + 2 * P) - (b0 + b1 + b2 + b3) ^ 2) / 2
      = 3 * P + (3 * (b0 ^ 2 + b1 ^ 2 + b2 ^ 2 + b3 ^ 2)
        - (b0 + b1 + b2 + b3) ^ 2) / 2 from by ring]
  by_cases hc : b0 + b1 + b2 + b3 ≤ 3/2
  · nlinarith [hsq, hP0, hc, hTn]
  · push Not at hc
    nlinarith [hsq, hP16, hc, hTle]

/-- First half of the charpoly certificate: c3^2 - 3c2 ≥ -11/16 for two-fractional order-4 standardized Laplacians. -/
theorem two_fractional_order_four_charpoly_certificate_D_bound (L : Matrix (Fin 4) (Fin 4) ℝ)
    (hL : is_standardized_laplacian_two_fractional 4 L) :
    -(11 / 16 : ℝ) ≤ (L.charpoly).coeff 3 ^ 2 - 3 * (L.charpoly).coeff 2 := by
  have hb : ∀ i j : Fin 4, i ≠ j → (0:ℝ) ≤ -L i j ∧ -L i j ≤ 1/4 := by
    intro i j hij
    have h := hL.1.2 i j hij
    constructor <;> linarith [h.1, h.2]
  have hr : ∀ i : Fin 4, L i 0 + L i 1 + L i 2 + L i 3 = 0 := by
    intro i; have h := hL.1.1 i; simpa [Fin.sum_univ_four] using h
  have hc3 : (L.charpoly).coeff 3 = -L.trace := by
    have h := Matrix.trace_eq_neg_charpoly_coeff (M := L)
    simp only [Fintype.card_fin] at h; linarith
  have hc2 := two_fractional_order_four_charpoly_certificate_D_bound_coeff_two L
  have hgoal : (L.charpoly).coeff 3 ^ 2 - 3 * (L.charpoly).coeff 2
      = (3 * (L * L).trace - L.trace ^ 2) / 2 := by rw [hc3, hc2]; ring
  rw [hgoal]
  have hd0 : L 0 0 = (-L 0 1) + (-L 0 2) + (-L 0 3) := by linarith [hr 0]
  have hd1 : L 1 1 = (-L 1 0) + (-L 1 2) + (-L 1 3) := by linarith [hr 1]
  have hd2 : L 2 2 = (-L 2 0) + (-L 2 1) + (-L 2 3) := by linarith [hr 2]
  have hd3 : L 3 3 = (-L 3 0) + (-L 3 1) + (-L 3 2) := by linarith [hr 3]
  have htr : (L * L).trace = L 0 0 ^ 2 + L 1 1 ^ 2 + L 2 2 ^ 2 + L 3 3 ^ 2
      + 2 * ((-L 0 1) * (-L 1 0) + (-L 0 2) * (-L 2 0) + (-L 0 3) * (-L 3 0)
             + (-L 1 2) * (-L 2 1) + (-L 1 3) * (-L 3 1) + (-L 2 3) * (-L 3 2)) := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_four]
    ring
  have hT : L.trace = L 0 0 + L 1 1 + L 2 2 + L 3 3 := by
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_four]
  rw [htr, hT, hd0, hd1, hd2, hd3]
  obtain ⟨e01, e01'⟩ := hb 0 1 (by decide)
  obtain ⟨e02, e02'⟩ := hb 0 2 (by decide)
  obtain ⟨e03, e03'⟩ := hb 0 3 (by decide)
  obtain ⟨e10, e10'⟩ := hb 1 0 (by decide)
  obtain ⟨e12, e12'⟩ := hb 1 2 (by decide)
  obtain ⟨e13, e13'⟩ := hb 1 3 (by decide)
  obtain ⟨e20, e20'⟩ := hb 2 0 (by decide)
  obtain ⟨e21, e21'⟩ := hb 2 1 (by decide)
  obtain ⟨e23, e23'⟩ := hb 2 3 (by decide)
  obtain ⟨e30, e30'⟩ := hb 3 0 (by decide)
  obtain ⟨e31, e31'⟩ := hb 3 1 (by decide)
  obtain ⟨e32, e32'⟩ := hb 3 2 (by decide)
  refine two_fractional_order_four_charpoly_certificate_D_bound_numeric
    ((-L 0 1) + (-L 0 2) + (-L 0 3)) ((-L 1 0) + (-L 1 2) + (-L 1 3))
    ((-L 2 0) + (-L 2 1) + (-L 2 3)) ((-L 3 0) + (-L 3 1) + (-L 3 2))
    ((-L 0 1) * (-L 1 0) + (-L 0 2) * (-L 2 0) + (-L 0 3) * (-L 3 0)
      + (-L 1 2) * (-L 2 1) + (-L 1 3) * (-L 3 1) + (-L 2 3) * (-L 3 2))
    (by linarith) (by linarith) (by linarith) (by linarith)
    (by positivity) ?_ (by linarith)
  · have p01 : 0 ≤ (1/4 - (-L 0 1)) * (1/4 - (-L 1 0)) := mul_nonneg (by linarith) (by linarith)
    have p02 : 0 ≤ (1/4 - (-L 0 2)) * (1/4 - (-L 2 0)) := mul_nonneg (by linarith) (by linarith)
    have p03 : 0 ≤ (1/4 - (-L 0 3)) * (1/4 - (-L 3 0)) := mul_nonneg (by linarith) (by linarith)
    have p12 : 0 ≤ (1/4 - (-L 1 2)) * (1/4 - (-L 2 1)) := mul_nonneg (by linarith) (by linarith)
    have p13 : 0 ≤ (1/4 - (-L 1 3)) * (1/4 - (-L 3 1)) := mul_nonneg (by linarith) (by linarith)
    have p23 : 0 ≤ (1/4 - (-L 2 3)) * (1/4 - (-L 3 2)) := mul_nonneg (by linarith) (by linarith)
    nlinarith
