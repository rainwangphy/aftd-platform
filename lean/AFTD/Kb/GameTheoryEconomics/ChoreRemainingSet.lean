import AFTD.Prelude

/-!
# chore_remaining_set

Topic: fair_division   Node: 766ff94bb145

Provenance: formalization of a published result. Source: arXiv:2611.04884, Section 4, line 729

For m chores and n agents, the set V of remaining chores consists of all chores whose index is at least 2n.
-/

/-- The set of remaining chores V consisting of chores with index at least 2n. -/
def chore_remaining_set (m n : ℕ) : Finset (Fin m) := Finset.univ.filter (fun e => 2 * n ≤ e.val)
