import AFTD.Prelude
import AFTD.Kb.Tcs.IsStandardizedLaplacian

/-!
# is_standardized_laplacian_two_fractional

Topic: graphs   Node: a8da1ff2e1e9

Provenance: formalization of a published result. Source: arXiv:2610.14100 Proposition 17

A real matrix L of order n is a standardized Laplacian with at most two fractional entries per row if L is a standardized Laplacian and for every row i, the number of columns j ≠ i with -(1/n) < L i j < 0 is at most 2.
-/

/-- A standardized Laplacian matrix of order n where each row has at most two off-diagonal entries in (-1/n, 0). -/
def is_standardized_laplacian_two_fractional (n : ℕ) (L : Matrix (Fin n) (Fin n) ℝ) : Prop := is_standardized_laplacian n L ∧
  ∀ i : Fin n, ((Finset.univ.filter (fun j : Fin n => j ≠ i ∧ -(1 : ℝ) / n < L i j ∧ L i j < 0)).card ≤ 2)
