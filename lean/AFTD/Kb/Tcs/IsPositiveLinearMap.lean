import AFTD.Prelude

/-!
# is_positive_linear_map

Topic: quantum   Node: f9c477f5ab7d

Provenance: formalization of a published result. Source: arXiv:2610.37187 Def. 3

A linear map Φ on d × d complex matrices is positive if it maps every positive semidefinite matrix to a positive semidefinite matrix.
-/

/-- A linear map on d × d complex matrices is positive if it maps positive semidefinite matrices to positive semidefinite matrices. -/
def is_positive_linear_map (d : ℕ) (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop := open scoped ComplexOrder in ∀ (X : Matrix (Fin d) (Fin d) ℂ), X.PosSemidef → (Φ X).PosSemidef
