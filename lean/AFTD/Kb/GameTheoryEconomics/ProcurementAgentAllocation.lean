import AFTD.Prelude

/-!
# procurement_agent_allocation

Topic: mechanism_design   Node: 288cbb7a8db2

The total work an agent receives: the sum of the allocations to its identities.
-/

noncomputable def procurement_agent_allocation (alloc : List ℝ → ℕ → ℝ)
    (mine others : List ℝ) : ℝ :=
  ∑ j ∈ Finset.range mine.length, alloc (mine ++ others) j
