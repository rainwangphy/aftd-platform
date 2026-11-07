import AFTD.Prelude

/-!
# is_orthogonal_projection

Topic: quantum   Node: f23583fbd66a

Provenance: formalization of a published result. Source: arXiv:2610.37347 Sec. 'Incompatibility in proper subspaces'

A matrix P on C^d is an orthogonal projection if P is Hermitian and P^2 = P.
-/

/-- An orthogonal projection on C^d: a Hermitian idempotent matrix P. -/
def is_orthogonal_projection {d : ℕ} (P : Matrix (Fin d) (Fin d) ℂ) : Prop := P.IsHermitian ∧ P * P = P
