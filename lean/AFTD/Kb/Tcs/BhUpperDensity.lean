import AFTD.Prelude

/-!
# bh_upper_density

Topic: combinatorics   Node: 16dc2e299bd7

Provenance: formalization of a published result. Source: arXiv:2611.01871, Sec. 1, line 81 and line 112

For a set of natural numbers A and order h, the normalized upper density is the limit superior along atTop of |A ∩ {1, ..., n}| / n^(1/h) as n → ∞.
-/

open scoped Classical in
/-- The normalized upper limit limsup_{n → ∞} A(n) / n^(1/h) of a set A ⊆ ℕ. -/
noncomputable def bh_upper_density (h : ℕ) (A : Set ℕ) : ℝ := Filter.limsup (fun n : ℕ => (((Finset.Icc 1 n).filter (· ∈ A)).card : ℝ) / (n : ℝ) ^ ((1 : ℝ) / (h : ℝ))) Filter.atTop
