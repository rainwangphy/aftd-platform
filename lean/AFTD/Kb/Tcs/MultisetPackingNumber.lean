import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasiblePacking

/-!
# multiset_packing_number

Topic: combinatorics   Node: 07e98f746f83

Provenance: formalization of a published result. Source: arXiv:2611.15376 Sec. 4

For natural numbers r, s, t, h, the multiset packing number multiset_packing_number r s t h is the supremum of the cardinalities of all feasible packings of s-subsets of Fin r with t-subset codegree at most h.
-/

/-- The maximum size, counted with multiplicity, of a multiset of s-subsets of Fin r such that every t-subset belongs to at most h members. -/
noncomputable def multiset_packing_number (r s t h : ℕ) : ℕ :=
  sSup {n : ℕ | ∃ M : Multiset (Finset (Fin r)), is_feasible_packing r s t h M ∧ M.card = n}
