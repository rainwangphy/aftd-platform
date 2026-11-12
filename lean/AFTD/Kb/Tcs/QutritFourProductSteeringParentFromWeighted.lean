import AFTD.Prelude

/-!
# qutrit_four_product_steering_parent_from_weighted

Topic: quantum   Node: 543f35d76157

Provenance: helper lemma. Local compatibility helper for OP-693.

Steering any four-product state by three binary qutrit effects yields a finite positive joint parent, conditional on the weighted hidden-parent construction.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_productparent_product_assemblage_parent_of_weighted
    (n m : ℕ) (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin m → Fin 3 → ℂ) (w : Fin m → Fin n → ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hweighted : ∀ (Q : Fin m → Matrix (Fin n) (Fin n) ℂ)
      (r : Fin m → ℝ) (p : Fin 3 → Fin m → ℝ) (P : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = ∑ t, (star (v t) ⬝ᵥ v t).re • vecMulVec (w t) (star (w t)) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        ∑ t, (star (v t) ⬝ᵥ ((A j) *ᵥ v t)).re • vecMulVec (w t) (star (w t)) := by
  apply hweighted (fun t => vecMulVec (w t) (star (w t)))
    (fun t => (star (v t) ⬝ᵥ v t).re)
    (fun j t => (star (v t) ⬝ᵥ ((A j) *ᵥ v t)).re)
    (∑ t, (star (v t) ⬝ᵥ v t).re • vecMulVec (w t) (star (w t)))
  · intro t
    exact Matrix.posSemidef_vecMulVec_self_star _
  · rfl
  · intro t
    have h := (Matrix.PosSemidef.one : (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef).dotProduct_mulVec_nonneg (v t)
    have hr := (Complex.nonneg_iff.mp h).1
    simpa using hr
  · intro j t
    have hlo := (Complex.nonneg_iff.mp ((hA j).1.dotProduct_mulVec_nonneg (v t))).1
    have hhi := (Complex.nonneg_iff.mp ((hA j).2.dotProduct_mulVec_nonneg (v t))).1
    simp only [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re] at hhi
    exact ⟨hlo, by linarith⟩


private lemma in767_productparent_steer_four_products
    {n : ℕ} (A : Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ) (x y : Fin n) :
    (∑ i : Fin 3, ∑ j : Fin 3,
      (∑ t : Fin 4, (v t i * w t x) * star (v t j * w t y)) * A j i) =
      ∑ t : Fin 4, (star (v t) ⬝ᵥ (A *ᵥ v t)) * (w t x * star (w t y)) := by
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_three, Fin.sum_univ_four,
    star_mul]
  ring

private lemma in767_productparent_marginal_four_products
    {n : ℕ} (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ) (x y : Fin n) :
    (∑ i : Fin 3, ∑ t : Fin 4, (v t i * w t x) * star (v t i * w t y)) =
      ∑ t : Fin 4, (star (v t) ⬝ᵥ v t) * (w t x * star (w t y)) := by
  simp [dotProduct, Fin.sum_univ_three, Fin.sum_univ_four, star_mul]
  ring

theorem qutrit_four_product_steering_parent_from_weighted
    (n : ℕ) (A : Fin 3 → Matrix (Fin 3) (Fin 3) ℂ)
    (v : Fin 4 → Fin 3 → ℂ) (w : Fin 4 → Fin n → ℂ)
    (hA : ∀ j, (A j).PosSemidef ∧ (1-A j).PosSemidef)
    (hweighted : ∀ (Q : Fin 4 → Matrix (Fin n) (Fin n) ℂ)
      (r : Fin 4 → ℝ) (p : Fin 3 → Fin 4 → ℝ) (P : Matrix (Fin n) (Fin n) ℂ),
      (∀ t, (Q t).PosSemidef) → (∑ t, (r t) • Q t) = P →
      (∀ t, 0 ≤ r t) → (∀ j t, 0 ≤ p j t ∧ p j t ≤ r t) →
      ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
        (∀ s, (G s).PosSemidef) ∧ (∑ s, G s) = P ∧
        ∀ j : Fin 3, (∑ s, if s j then G s else 0) = ∑ t, (p j t) • Q t) :
    ∃ G : (Fin 3 → Bool) → Matrix (Fin n) (Fin n) ℂ,
      (∀ s, (G s).PosSemidef) ∧
      (∑ s, G s) = (fun x y => ∑ i : Fin 3, ∑ t : Fin 4,
        (v t i * w t x) * star (v t i * w t y)) ∧
      ∀ j : Fin 3, (∑ s, if s j then G s else 0) =
        (fun x y => ∑ i : Fin 3, ∑ k : Fin 3,
          (∑ t : Fin 4, (v t i * w t x) * star (v t k * w t y)) * A j k i) := by
  obtain ⟨G, hG, hsum, hmarg⟩ := in767_productparent_product_assemblage_parent_of_weighted n 4 A v w hA hweighted
  refine ⟨G, hG, ?_, ?_⟩
  · rw [hsum]
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul]
    rw [in767_productparent_marginal_four_products]
    apply Finset.sum_congr rfl
    intro t ht
    have hn := (Complex.nonneg_iff.mp ((Matrix.PosSemidef.one :
      (1 : Matrix (Fin 3) (Fin 3) ℂ).PosSemidef).dotProduct_mulVec_nonneg (v t))).2
    simp only [Matrix.one_mulVec] at hn
    have hr : (((star (v t) ⬝ᵥ v t).re : ℝ) : ℂ) = star (v t) ⬝ᵥ v t := by
      apply Complex.ext <;> simp [hn]
    rw [Complex.real_smul, hr]
  · intro j
    rw [hmarg j]
    ext x y
    simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, Pi.star_apply,
      smul_eq_mul]
    rw [in767_productparent_steer_four_products]
    apply Finset.sum_congr rfl
    intro t ht
    have hn := (Complex.nonneg_iff.mp ((hA j).1.dotProduct_mulVec_nonneg (v t))).2
    have hr : (((star (v t) ⬝ᵥ (A j *ᵥ v t)).re : ℝ) : ℂ) =
        star (v t) ⬝ᵥ (A j *ᵥ v t) := by
      apply Complex.ext <;> simp [hn]
    rw [Complex.real_smul, hr]
