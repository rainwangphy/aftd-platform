import AFTD.Prelude

/-!
# DirectMechanism

Topic: mechanism_design   Node: 6eb636141e82

A direct mechanism with player type Player, type spaces Theta i for each player i : Player, and outcome type Outcome, consists of an allocation rule allocation : (∀ i : Player, Theta i) → Outcome and a payment rule payment : Player → (∀ i : Player, Theta i) → ℝ.
-/

/-- A direct mechanism consists of an allocation rule and a profile of payment rules for each player. -/
structure DirectMechanism (Player : Type*) (Theta : Player → Type*) (Outcome : Type*) where
  allocation : (∀ i, Theta i) → Outcome
  payment : Player → (∀ i, Theta i) → ℝ
