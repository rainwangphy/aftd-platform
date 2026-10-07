import AFTD.Prelude
import AFTD.Kb.Tcs.Tensor3Pure

/-!
# linear_flattening_potency_gt

Topic: algebraic_complexity   Node: 055ae16b1bb6

Provenance: formalization of a published result. Source: arXiv:2610.08504 (Explicit tensors beyond the linear flattening barrier), Eq. (1.2) (potency of a linear flattening)

A linear flattening L : ℂⁿ ⊗ ℂⁿ ⊗ ℂⁿ → Mat_{u×v}(ℂ) has potency greater than r: some tensor T has rank L(T) > r · ρ(L), where ρ(L) = max_{x,y,z} rank L(x ⊗ y ⊗ z). (Equivalently Pot(L) = max_T rank L(T) / ρ(L) > r; for L = 0 the condition fails.)
-/

/-- The linear flattening `L : ℂⁿ ⊗ ℂⁿ ⊗ ℂⁿ → Mat_{u×v}(ℂ)` has potency greater than `r`: some tensor `T` has `rank L(T) > r · ρ(L)`, where `ρ(L)` is the largest rank of `L` on a pure tensor `x ⊗ y ⊗ z`. -/
def linear_flattening_potency_gt {n u v : ℕ}
    (L : (Fin n → Fin n → Fin n → ℂ) →ₗ[ℂ] Matrix (Fin u) (Fin v) ℂ) (r : ℕ) : Prop :=
  ∃ T, ∀ x y z : Fin n → ℂ, r * (L (tensor3_pure x y z)).rank < (L T).rank
