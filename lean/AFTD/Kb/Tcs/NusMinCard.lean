import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetHasNoUniqueSums

/-!
# nus_min_card

Topic: combinatorics   Node: 8b56438d0db0

Provenance: formalization of a published result. Source: arXiv:2610.09349 (A near-quadratic lower bound for sets with no unique sums), Sec. 1 (m(p) = min{|A| : A ⊆ F_p NUS}); written as an infimum over subsets of ZMod p.

m(p): the least size of a subset of Z/pZ with no unique sums.
-/

/-- `m(p)`: the least size of a subset of `ZMod p` with no unique sums. -/
noncomputable def nus_min_card (p : ℕ) : ℕ :=
  sInf {k | ∃ A : Finset (ZMod p), finset_has_no_unique_sums A ∧ A.card = k}
