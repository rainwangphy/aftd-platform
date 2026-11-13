import AFTD.Prelude

/-!
# hypergraph_deficit_h

Topic: quantum_mechanics   Node: 515a9392be14

Provenance: formalization of a published result. Source: arXiv:2610.42129, OP-1668

For any real number p and natural number j, hypergraph_deficit_h p j is defined as 4 * p ^ j * (1 - p) ^ j / (p ^ j + (1 - p) ^ j) ^ 2.
-/

/-- Kernel function h_p(j) = 4 p^j (1-p)^j / (p^j + (1-p)^j)^2 for the hypergraph metrology deficit. -/
noncomputable def hypergraph_deficit_h (p : ℝ) (j : ℕ) : ℝ := 4 * p ^ j * (1 - p) ^ j / (p ^ j + (1 - p) ^ j) ^ 2
