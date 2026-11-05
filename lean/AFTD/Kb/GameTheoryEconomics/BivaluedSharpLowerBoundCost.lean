import AFTD.Prelude

/-!
# bivalued_sharp_lower_bound_cost

Topic: fair_division   Node: a87fa7c10c15

Provenance: formalization of a published result. Source: knowledgebase (OP-1112)

The lower-bound chore cost profile with n agents and n+1 chores, where agents 0 through n-2 assign cost 1 to chores 0 and 1, agent n-1 assigns cost 1 to chores 0 and 2, and all other costs are r.
-/

/-- The n-agent, (n+1)-chore lower bound profile with low costs on {0,1} for agents < n-1 and {0,2} for agent n-1. -/
def bivalued_sharp_lower_bound_cost (n : ℕ) (r : ℝ) : Fin n → Fin (n + 1) → ℝ := fun i g =>
    if (i.val < n - 1 ∧ (g.val = 0 ∨ g.val = 1)) ∨
       (i.val = n - 1 ∧ (g.val = 0 ∨ g.val = 2)) then
      1
    else
      r
