import AFTD.Prelude

/-!
# elem_symm

Topic: combinatorics   Node: 852a696cb619

Provenance: formalization of a published result. Source: Macdonald, Symmetric Functions and Hall Polynomials, Ch. 1

The k-th elementary symmetric polynomial evaluated on a vector v : Fin n → ℝ is the sum over all subsets of Fin n of size k of the product of the entries indexed by that subset.
-/

/-- The k-th elementary symmetric sum of a vector of real numbers indexed by Fin n. -/
def elem_symm {n : ℕ} (k : ℕ) (v : Fin n → ℝ) : ℝ := ∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard k, ∏ i ∈ s, v i
