import AFTD.Prelude

/-!
# sumset_finset_sorted_vector

Topic: combinatorics   Node: 72399ae95a05

Provenance: original. Related work: arXiv:2611.07303, Section 5 (line 1263)

For a natural number k and a finset A of integers, sumset_finset_sorted_vector k A is the vector in Fin k → ℤ whose entries are the elements of A in strictly increasing order if A has cardinality k, and 0 otherwise.
-/

/-- The vector of elements of a finite set of integers of size k in strictly increasing order. -/
def sumset_finset_sorted_vector (k : ℕ) (A : Finset ℤ) : Fin k → ℤ := if h : A.card = k then A.orderEmbOfFin h else 0
