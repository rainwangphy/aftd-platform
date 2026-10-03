import AFTD.Prelude

/-!
# procurement_agent_utility

Topic: mechanism_design   Node: 52791c820f1f

The utility of an agent with cost c who submits the bids `mine` (one per identity) while all other identities bid `others`: the sum over its identities of payment minus c times allocated work.
-/

/-- Utility of an agent with cost `c` whose identities bid `mine` while all other identities bid `others` (the agent's identities are listed first). -/
noncomputable def procurement_agent_utility (alloc pay : List ℝ → ℕ → ℝ) (c : ℝ)
    (mine others : List ℝ) : ℝ :=
  ∑ j ∈ Finset.range mine.length, (pay (mine ++ others) j - c * alloc (mine ++ others) j)
