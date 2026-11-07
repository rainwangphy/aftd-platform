import AFTD.Prelude

/-!
# is_proper_orthogonal_projection

Topic: quantum   Node: 8fdc8404454d

Provenance: formalization of a published result. Source: arXiv:2610.37347 Sec. 'Incompatibility in proper subspaces'

A matrix P on C^d is a proper orthogonal projection if P is Hermitian, P^2 = P, and the rank of P is strictly less than d.
-/

/-- A proper orthogonal projection on C^d: an orthogonal projection P with rank strictly less than d. -/
def is_proper_orthogonal_projection {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) : Prop := P.IsHermitian ∧ P * P = P ∧ P.rank < d
