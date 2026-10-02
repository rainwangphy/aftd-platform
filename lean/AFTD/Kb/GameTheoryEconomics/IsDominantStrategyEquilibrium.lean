import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism

/-!
# is_dominant_strategy_equilibrium

Topic: mechanism_design   Node: 73edb4637844

A strategy profile s : (i : Player) → Theta i → Message i is a dominant-strategy equilibrium of mechanism M under valuation profile v if for every player i, true type θ_i : Theta i, message profile m : ∀ j, Message j, and alternative message m_i' : Message i, playing s i θ_i yields weakly higher utility than playing m_i': v i θ_i (M.allocation (Function.update m i m_i')) - M.payment i (Function.update m i m_i') ≤ v i θ_i (M.allocation (Function.update m i (s i θ_i))) - M.payment i (Function.update m i (s i θ_i)).
-/

/-- A strategy profile s is a dominant-strategy equilibrium if reporting according to s yields weakly higher utility than any deviating message, against any message profile. -/
def is_dominant_strategy_equilibrium
    {Player : Type*} [DecidableEq Player]
    {Message : Player → Type*} {Theta : Player → Type*} {Outcome : Type*}
    (M : DirectMechanism Player Message Outcome)
    (s : (i : Player) → Theta i → Message i)
    (v : (i : Player) → Theta i → Outcome → ℝ) : Prop := ∀ (i : Player) (θ_i : Theta i) (m : ∀ j, Message j) (m_i' : Message i),
    v i θ_i (M.allocation (Function.update m i m_i')) - M.payment i (Function.update m i m_i') ≤
    v i θ_i (M.allocation (Function.update m i (s i θ_i))) - M.payment i (Function.update m i (s i θ_i))
