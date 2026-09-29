import AFTD.Prelude

/-!
# StrategicGame

Topic: equilibria   Node: 24fc9c28b99d

A strategic-form game with player type Player consists of a family of strategy types Strategy i for each player i : Player, and a real-valued payoff function payoff i : (∀ j : Player, Strategy j) → ℝ for each player i : Player.
-/

/-- A strategic-form (normal-form) game with player type `Player`. -/
structure StrategicGame (Player : Type*) where
  Strategy : Player → Type*
  payoff : (i : Player) → (∀ j, Strategy j) → ℝ
