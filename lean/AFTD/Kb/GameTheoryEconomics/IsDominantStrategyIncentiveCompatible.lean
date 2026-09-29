import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism

/-!
# is_dominant_strategy_incentive_compatible

Topic: mechanism_design   Node: 8aff4e206fa9

For a direct mechanism (M : DirectMechanism Player Theta Outcome) with {Player : Type*} [DecidableEq Player], {Theta : Player → Type*}, {Outcome : Type*}, and valuation profile (v : (i : Player) → Theta i → Outcome → ℝ), is_dominant_strategy_incentive_compatible M v is defined with body := ∀ (i : Player) (θ : ∀ j, Theta j) (θ_i' : Theta i), v i (θ i) (M.allocation (Function.update θ i θ_i')) - M.payment i (Function.update θ i θ_i') ≤ v i (θ i) (M.allocation θ) - M.payment i θ.
-/

/-- Dominant-strategy incentive compatibility (strategy-proofness) for a direct mechanism. -/
def is_dominant_strategy_incentive_compatible
    {Player : Type*} [DecidableEq Player] {Theta : Player → Type*} {Outcome : Type*}
    (M : DirectMechanism Player Theta Outcome)
    (v : (i : Player) → Theta i → Outcome → ℝ) : Prop := ∀ (i : Player) (θ : ∀ j, Theta j) (θ_i' : Theta i),
    v i (θ i) (M.allocation (Function.update θ i θ_i')) - M.payment i (Function.update θ i θ_i') ≤
    v i (θ i) (M.allocation θ) - M.payment i θ
