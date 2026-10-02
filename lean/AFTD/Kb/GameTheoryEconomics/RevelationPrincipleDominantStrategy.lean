import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism
import AFTD.Kb.GameTheoryEconomics.InducedDirectMechanism
import AFTD.Kb.GameTheoryEconomics.IsDominantStrategyEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsDominantStrategyIncentiveCompatible

/-!
# revelation_principle_dominant_strategy

Topic: mechanism_design   Node: 4726235e2d21

The Revelation Principle for dominant-strategy equilibrium: if s is a dominant-strategy equilibrium of mechanism M with respect to valuation profile v, then the induced direct mechanism induced_direct_mechanism M s is dominant-strategy incentive-compatible (is_dominant_strategy_incentive_compatible).
-/

/-- The Revelation Principle: if s is a dominant-strategy equilibrium of mechanism M, the induced direct mechanism is dominant-strategy incentive-compatible. -/
theorem revelation_principle_dominant_strategy
    {Player : Type*} [DecidableEq Player]
    {Message : Player → Type*} {Theta : Player → Type*} {Outcome : Type*}
    (M : DirectMechanism Player Message Outcome)
    (s : (i : Player) → Theta i → Message i)
    (v : (i : Player) → Theta i → Outcome → ℝ)
    (hs : is_dominant_strategy_equilibrium M s v) :
    is_dominant_strategy_incentive_compatible (induced_direct_mechanism M s) v := by
  intro i θ θ_i'
  have h_dev := hs i (θ i) (fun j => s j (θ j)) (s i θ_i')
  have h1 : (fun j => s j (Function.update θ i θ_i' j)) =
      Function.update (fun j => s j (θ j)) i (s i θ_i') := by
    ext j
    by_cases h : j = i
    · subst h; simp
    · simp [h]
  rw [Function.update_eq_self i (fun j => s j (θ j))] at h_dev
  dsimp [induced_direct_mechanism]
  rw [h1]
  exact h_dev
