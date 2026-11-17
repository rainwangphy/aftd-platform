import AFTD.Prelude

/-!
# is_dichotomic_projective_observable

Topic: quantum   Node: 1f0f07758a41

Provenance: formalization of a published result. Source: arXiv:2610.35838 Sec. II.3

A dichotomic projective observable on the Hilbert space ℂ^d is a Hermitian d × d complex matrix B whose matrix product with itself B * B is the identity matrix.
-/

/-- A dichotomic projective observable on C^d is a Hermitian matrix squaring to the identity. -/
def is_dichotomic_projective_observable {d : ℕ} (B : Matrix (Fin d) (Fin d) ℂ) : Prop := B.IsHermitian ∧ B * B = 1
