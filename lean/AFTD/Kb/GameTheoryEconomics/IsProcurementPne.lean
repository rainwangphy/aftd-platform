import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProcurementAgentUtility
import AFTD.Kb.GameTheoryEconomics.ProcurementOthersBids

/-!
# is_procurement_pne

Topic: mechanism_design   Node: cc8467b3ffb2

A profile of (multi-)bids is a pure Nash equilibrium of the procurement game if all bids are nonnegative and no agent can gain by switching to any other nonnegative list of bids.
-/

def is_procurement_pne (alloc pay : List ℝ → ℕ → ℝ) {n : ℕ} (c : Fin n → ℝ)
    (β : Fin n → List ℝ) : Prop :=
  (∀ i, ∀ b ∈ β i, 0 ≤ b) ∧
    ∀ i (σ : List ℝ), (∀ b ∈ σ, 0 ≤ b) →
      procurement_agent_utility alloc pay (c i) σ (procurement_others_bids β i) ≤
        procurement_agent_utility alloc pay (c i) (β i) (procurement_others_bids β i)
