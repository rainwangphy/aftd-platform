import AFTD.Prelude

/-!
# has_kraus_representation

Topic: quantum   Node: 0be5fed02425

Provenance: formalization of a published result. Source: arXiv:2610.37187, Section 7

A linear map on d × d complex matrices has a Kraus representation if it can be written as X ↦ ∑ᵢ Kᵢ X Kᵢ† for finitely many Kraus operators Kᵢ.
-/

/-- A linear map on d × d complex matrices has a Kraus representation (i.e. is completely positive). -/
def has_kraus_representation (d : ℕ) (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℂ] Matrix (Fin d) (Fin d) ℂ) : Prop :=
  ∃ (m : ℕ) (K : Fin m → Matrix (Fin d) (Fin d) ℂ),
    ∀ X, Φ X = ∑ i, K i * X * star (K i)
