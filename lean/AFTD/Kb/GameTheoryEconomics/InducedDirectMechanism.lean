import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.DirectMechanism

/-!
# induced_direct_mechanism

Topic: mechanism_design   Node: df36b3916f1c

Given a mechanism M with player type Player, message types Message, and outcome type Outcome, and a strategy profile s mapping each player's type in Theta i to a message in Message i, the induced direct mechanism induced_direct_mechanism M s has type spaces Theta, allocation rule fun θ => M.allocation (fun j => s j (θ j)), and payment rule fun i θ => M.payment i (fun j => s j (θ j)).
-/

/-- The direct revelation mechanism induced by a mechanism M and a strategy profile s. -/
def induced_direct_mechanism
    {Player : Type*} {Message : Player → Type*} {Theta : Player → Type*} {Outcome : Type*}
    (M : DirectMechanism Player Message Outcome)
    (s : (i : Player) → Theta i → Message i) :
    DirectMechanism Player Theta Outcome := {
  allocation := fun θ => M.allocation (fun j => s j (θ j))
  payment := fun i θ => M.payment i (fun j => s j (θ j))
}
