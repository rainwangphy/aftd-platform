import AFTD.Prelude

/-!
# tensor3_pure

Topic: algebraic_complexity   Node: deaf0332301e

Provenance: formalization of a published result. Source: arXiv:2610.08504 (Explicit tensors beyond the linear flattening barrier), Sec. 1 (rank-one tensors)

The pure tensor x ⊗ y ⊗ z in ℂⁿ ⊗ ℂⁿ ⊗ ℂⁿ, with entries x_i y_j z_k.
-/

/-- The pure tensor `x ⊗ y ⊗ z` in `ℂⁿ ⊗ ℂⁿ ⊗ ℂⁿ`, with entries `xᵢ yⱼ zₖ`. -/
def tensor3_pure {n : ℕ} (x y z : Fin n → ℂ) : Fin n → Fin n → Fin n → ℂ :=
  fun i j k => x i * y j * z k
