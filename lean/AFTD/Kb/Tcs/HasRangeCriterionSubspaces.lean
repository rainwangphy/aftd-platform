import AFTD.Prelude

/-!
# has_range_criterion_subspaces

Topic: quantum   Node: 5bb579e42b7d

Provenance: formalization of a published result. Source: arXiv:2611.08518 Problem 1.1

There exist complex linear subspaces D and E in C^m ⊗ C^n of codimensions k and ℓ, respectively, such that for all x ∈ C^m and y ∈ C^n, if x ⊗ y ∈ D and star x ⊗ y ∈ E, then x = 0 or y = 0.
-/

open scoped TensorProduct in
/-- Predicate that there exist complex subspaces D, E in C^m ⊗ C^n of codimensions k and ℓ satisfying the range criterion. -/
def has_range_criterion_subspaces (m n k ℓ : ℕ) : Prop :=
  ∃ (D : Submodule ℂ (TensorProduct ℂ (Fin m → ℂ) (Fin n → ℂ)))
    (E : Submodule ℂ (TensorProduct ℂ (Fin m → ℂ) (Fin n → ℂ))),
    Module.finrank ℂ ((TensorProduct ℂ (Fin m → ℂ) (Fin n → ℂ)) ⧸ D) = k ∧
    Module.finrank ℂ ((TensorProduct ℂ (Fin m → ℂ) (Fin n → ℂ)) ⧸ E) = ℓ ∧
    ∀ (x : Fin m → ℂ) (y : Fin n → ℂ),
      x ⊗ₜ[ℂ] y ∈ D → star x ⊗ₜ[ℂ] y ∈ E → x = 0 ∨ y = 0
