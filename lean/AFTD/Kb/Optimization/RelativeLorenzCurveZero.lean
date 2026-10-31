import AFTD.Prelude
import AFTD.Kb.Optimization.RelativeLorenzCurve

/-!
# relative_lorenz_curve_zero

Topic: submodular   Node: d2199c2b7e27

Provenance: helper lemma. arXiv:2610.35433:874

For any natural number n, population vector x in stdSimplex ℝ (Fin n), and strictly positive Gibbs vector γ in stdSimplex ℝ (Fin n), the relative Lorenz curve relative_lorenz_curve x γ 0 equals 0.
-/

/-- The relative Lorenz curve evaluates to 0 at t = 0. -/
theorem relative_lorenz_curve_zero {n : ℕ} {x γ : Fin n → ℝ}
    (hx : x ∈ stdSimplex ℝ (Fin n)) (hγ : γ ∈ stdSimplex ℝ (Fin n)) (hγ_pos : ∀ i, 0 < γ i) :
    relative_lorenz_curve x γ 0 = 0 := by
  unfold relative_lorenz_curve
  have h_set : {α : Fin n → ℝ | (∀ i, 0 ≤ α i ∧ α i ≤ 1) ∧ ∑ i, α i * γ i ≤ 0} = {(0 : Fin n → ℝ)} := by
    ext α
    simp only [Set.mem_singleton_iff]
    constructor
    · rintro ⟨h1, h2⟩
      ext i
      have h_nonneg : ∀ j, 0 ≤ α j * γ j := fun j => mul_nonneg (h1 j).1 (le_of_lt (hγ_pos j))
      have : α i * γ i ≤ ∑ j, α j * γ j := Finset.single_le_sum (fun j _ => h_nonneg j) (Finset.mem_univ i)
      have h_i_nonneg := h_nonneg i
      have h_term : α i * γ i = 0 := by linarith
      cases mul_eq_zero.mp h_term with
      | inl ha => exact ha
      | inr hg => exact (ne_of_gt (hγ_pos i) hg).elim
    · rintro rfl
      simp
  rw [h_set, Set.image_singleton]
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  exact csSup_singleton 0
