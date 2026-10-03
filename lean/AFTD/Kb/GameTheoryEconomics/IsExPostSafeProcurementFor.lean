import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility

/-!
# is_ex_post_safe_procurement_for

Topic: mechanism_design   Node: 2778fe16fdbb

A procurement mechanism is ex-post safe for an agent of cost c if some bidding strategy guarantees nonnegative utility against all other bids and strictly positive utility against some.
-/

def is_ex_post_safe_procurement_for (alloc pay : List ℝ → ℕ → ℝ) (c : ℝ) : Prop :=
  ∃ mine : List ℝ, (∀ b ∈ mine, 0 ≤ b) ∧
    (∀ others : List ℝ, (∀ x ∈ others, 0 ≤ x) →
      0 ≤ procurement_agent_utility alloc pay c mine others) ∧
    ∃ others : List ℝ, (∀ x ∈ others, 0 ≤ x) ∧
      0 < procurement_agent_utility alloc pay c mine others
