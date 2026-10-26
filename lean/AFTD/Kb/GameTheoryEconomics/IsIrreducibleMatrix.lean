import AFTD.Prelude

/-!
# is_irreducible_matrix

Topic: combinatorial_games   Node: 3b3bd076a07a

Provenance: formalization of a published result. Source: arXiv:2610.08949 line 199

A rational matrix P : Matrix (Fin n) (Fin n) ℚ is irreducible if for all i j : Fin n, there exists a natural number m such that 0 < (P ^ m) i j.
-/

/-- Irreducibility of a rational transition matrix: every state is reachable from every other state. -/
def is_irreducible_matrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) : Prop := ∀ i j : Fin n, ∃ m : ℕ, 0 < (P ^ m) i j
