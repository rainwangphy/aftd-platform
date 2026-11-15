import AFTD.Prelude

/-!
# thermomajorization_diff

Topic: quantum_mechanics   Node: 0e7dfdaaacce

Provenance: formalization of a published result. Source: arXiv:2610.35433

For population vectors x and y in ℝⁿ and an index j : ℕ, thermomajorization_diff x y j is the prefix difference ∑_{i < j} (y i - x i) summing y i - x i over all indices i : Fin n with (i : ℕ) < j.
-/

/-- Prefix differences between population vectors. -/
def thermomajorization_diff {n : ℕ} (x y : Fin n → ℝ) (j : ℕ) : ℝ := ∑ i ∈ Finset.filter (fun (i : Fin n) => (i : ℕ) < j) Finset.univ, (y i - x i)
