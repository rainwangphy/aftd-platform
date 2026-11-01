import AFTD.Prelude

/-!
# dual_melas_shift_equiv

Topic: information   Node: 17234a2a8a91

Provenance: formalization of a published result. Source: arXiv:2610.38017 Definition 3

Two binary polynomials f and g are shift-equivalent modulo the product of the minimal polynomials of α and α⁻¹ over 𝔽₂ if there exists a natural number j such that (minpoly 𝔽₂ α) * (minpoly 𝔽₂ α⁻¹) divides f - X^j * g.
-/

/-- Shift equivalence of binary polynomials modulo the product of minimal polynomials of α and α⁻¹. -/
def dual_melas_shift_equiv {F : Type*} [Field F] [Algebra (ZMod 2) F]
    (α : F) (f g : Polynomial (ZMod 2)) : Prop := ∃ j : ℕ, minpoly (ZMod 2) α * minpoly (ZMod 2) α⁻¹ ∣ f - Polynomial.X ^ j * g
