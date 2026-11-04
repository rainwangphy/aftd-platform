import AFTD.Prelude

/-!
# bh_counting

Topic: combinatorics   Node: e25ed60ef16e

Provenance: formalization of a published result. Source: arXiv:2611.01871, Sec. 1, line 96

For a set of natural numbers A and a positive integer n, A(n) is the cardinality of A ∩ {1, ..., n}.
-/

open scoped Classical in
/-- The counting function A(n) = |A ∩ [1, n]| of a set A ⊆ ℕ. -/
noncomputable def bh_counting (A : Set ℕ) (n : ℕ) : ℕ := ((Finset.Icc 1 n).filter (· ∈ A)).card
