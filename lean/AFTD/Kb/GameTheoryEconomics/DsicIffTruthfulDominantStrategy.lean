import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism
import AFTD.Kb.GameTheoryEconomics.InducedDirectMechanism
import AFTD.Kb.GameTheoryEconomics.IsDominantStrategyEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsDominantStrategyIncentiveCompatible
import AFTD.Kb.GameTheoryEconomics.RevelationPrincipleDominantStrategy

/-!
# dsic_iff_truthful_dominant_strategy

Topic: mechanism_design   Node: c87f37ab4976

For any direct mechanism M and valuation profile v, truthful reporting (the identity strategy profile fun _ => id) is a dominant-strategy equilibrium of M if and only if M is dominant-strategy incentive-compatible.
-/

/-- A direct mechanism is dominant-strategy incentive-compatible if and only if truthful reporting is a dominant-strategy equilibrium. -/
theorem dsic_iff_truthful_dominant_strategy
    {Player : Type*} [DecidableEq Player]
    {Theta : Player → Type*} {Outcome : Type*}
    (M : DirectMechanism Player Theta Outcome)
    (v : (i : Player) → Theta i → Outcome → ℝ) :
    is_dominant_strategy_equilibrium M (fun _ => id) v ↔
    is_dominant_strategy_incentive_compatible M v := by
  constructor
  · intro h i θ θ_i'
    have h1 := h i (θ i) θ θ_i'
    dsimp at h1
    rw [Function.update_eq_self] at h1
    exact h1
  · intro h i θ_i m m_i'
    have h1 := h i (Function.update m i θ_i) m_i'
    rw [Function.update_self] at h1
    rw [Function.update_idem] at h1
    exact h1
