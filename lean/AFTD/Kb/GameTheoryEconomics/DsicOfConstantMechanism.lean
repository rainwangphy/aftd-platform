import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism
import AFTD.Kb.GameTheoryEconomics.IsDominantStrategyIncentiveCompatible

/-!
# dsic_of_constant_mechanism

Topic: mechanism_design   Node: 0fef50d750f6

Provenance: original. Related work: machine-posed degenerate case of DSIC (constant mechanism); trivial, folklore in mechanism design, no novelty claimed

A constant direct mechanism, which chooses a fixed allocation and charges a fixed payment regardless of reports, is dominant-strategy incentive-compatible for any valuation function.
-/

/-- A constant direct mechanism is dominant strategy incentive compatible for any valuation profile. -/
theorem dsic_of_constant_mechanism {Player : Type*} [DecidableEq Player]
    {Theta : Player → Type*} {Outcome : Type*}
    (c_alloc : Outcome) (c_pay : ℝ)
    (v : (i : Player) → Theta i → Outcome → ℝ) :
    is_dominant_strategy_incentive_compatible
      ⟨fun _ => c_alloc, fun _ _ => c_pay⟩ v := by
  intro i θ θ_i'
  dsimp [is_dominant_strategy_incentive_compatible]
  linarith
