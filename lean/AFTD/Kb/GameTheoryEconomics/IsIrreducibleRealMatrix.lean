import AFTD.Prelude

/-!
# is_irreducible_real_matrix

Topic: combinatorial_games   Node: 7545fc2ee122

Provenance: formalization of a published result. Source: scout/2610-08949-primitive-periods-in-greedy-chip-firing-games.md:199

A real matrix P : Matrix (Fin n) (Fin n) ℝ is irreducible if for every pair of indices i, j : Fin n, there exists a natural number m such that (P ^ m) i j > 0.
-/

/-- A real square matrix P on Fin n is irreducible if for all states i and j there is a power m with positive (i, j)-th entry. -/
def is_irreducible_real_matrix {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j : Fin n, ∃ m : ℕ, 0 < (P ^ m) i j
