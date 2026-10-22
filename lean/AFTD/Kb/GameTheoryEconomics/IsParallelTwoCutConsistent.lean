import AFTD.Prelude

/-!
# is_parallel_two_cut_consistent

Topic: fair_division   Node: a249c6661d0b

Provenance: formalization of a published result. Source: arXiv:2610.27956, Section 1.1 and Section 4.1

Given a finite set of points P in ℝ × ℝ, an ℝ-linear map φ : (ℝ × ℝ) →ₗ[ℝ] ℝ, two thresholds t₁, t₂ ∈ ℝ, and an assignment function α : (ℝ × ℝ) → Fin 3, is_parallel_two_cut_consistent P φ t₁ t₂ α is defined as: t₁ ≤ t₂ and for every point p ∈ P, (1) if α(p) = 0 then φ(p) ≤ t₁, (2) if α(p) = 1 then t₁ ≤ φ(p) and φ(p) ≤ t₂, and (3) if α(p) = 2 then t₂ ≤ φ(p).
-/

/-- An assignment of points to three regions is consistent with two parallel cuts at thresholds t₁ ≤ t₂ along linear functional φ. -/
def is_parallel_two_cut_consistent (P : Finset (ℝ × ℝ)) (φ : (ℝ × ℝ) →ₗ[ℝ] ℝ) (t₁ t₂ : ℝ)
    (α : (ℝ × ℝ) → Fin 3) : Prop := t₁ ≤ t₂ ∧ ∀ p ∈ P, (α p = 0 → φ p ≤ t₁) ∧ (α p = 1 → t₁ ≤ φ p ∧ φ p ≤ t₂) ∧ (α p = 2 → t₂ ≤ φ p)
