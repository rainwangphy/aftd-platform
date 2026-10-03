import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility

/-!
# is_sybil_proof_procurement

Topic: mechanism_design   Node: 8f8e366fdd65

A procurement mechanism is Sybil-proof if, for every cost and every multi-bid strategy, some single bid does at least as well against every profile of other bids.
-/

def is_sybil_proof_procurement (alloc pay : List ℝ → ℕ → ℝ) : Prop :=
  ∀ (c : ℝ), 0 ≤ c → ∀ mine : List ℝ, (∀ b ∈ mine, 0 ≤ b) →
    ∃ b : ℝ, 0 ≤ b ∧ ∀ others : List ℝ, (∀ x ∈ others, 0 ≤ x) →
      procurement_agent_utility alloc pay c mine others ≤
        procurement_agent_utility alloc pay c [b] others
