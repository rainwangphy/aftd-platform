import AFTD.Prelude

/-!
# uniform_bivalued_obstruction_cost

Topic: fair_division   Node: c1dfa20aded3

Provenance: formalization of a published result. Source: OP-1697

The two-agent chore cost profile on 4t chores where agent 0 assigns cost 1 to every chore, while agent 1 assigns cost r to 2t - 1 high chores and cost 1 to 2t + 1 low chores.
-/

/-- The 4t-chore obstruction instance where agent 0 assigns cost 1 to all chores and agent 1 assigns cost r to 2t-1 chores and cost 1 to 2t+1 chores. -/
def uniform_bivalued_obstruction_cost (t : ℕ) (r : ℝ) : Fin 2 → Fin (4 * t) → ℝ := fun i g => if i = 0 then 1 else if g.val < 2 * t - 1 then r else 1
