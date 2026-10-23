import AFTD.Prelude

/-!
# is_standardized_laplacian

Topic: graphs   Node: acd28055212c

Provenance: formalization of a published result. Source: scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:155

A standardized Laplacian matrix of order n is a real n x n matrix with zero row sums and off-diagonal entries in [-1/n, 0].
-/

/-- Predicate for a real n x n matrix being a standardized Laplacian matrix. -/
def is_standardized_laplacian (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) : Prop := (∀ i : Fin n, ∑ j : Fin n, L i j = 0) ∧
   (∀ i j : Fin n, i ≠ j → -(1 : ℝ) / n ≤ L i j ∧ L i j ≤ 0)
