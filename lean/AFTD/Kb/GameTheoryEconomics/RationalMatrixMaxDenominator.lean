import AFTD.Prelude

/-!
# rational_matrix_max_denominator

Topic: combinatorial_games   Node: 87df15ac56dc

Provenance: formalization of a published result. Source: arXiv:2610.08949

For a natural number n and a rational matrix P : Matrix (Fin n) (Fin n) ℚ, rational_matrix_max_denominator P is the maximum of 1 and all entry denominators (P i j).den for (i, j) : Fin n × Fin n, computed by folding max starting at 1 over Finset.univ.
-/

/-- The maximum denominator of the rational entries in transition matrix P. -/
def rational_matrix_max_denominator {n : ℕ} (P : Matrix (Fin n) (Fin n) ℚ) : ℕ := Finset.fold max 1 (fun (ij : Fin n × Fin n) => (P ij.1 ij.2).den) Finset.univ
