import AFTD.Prelude

/-!
# team_T2

Topic: algorithms   Node: 3df570a9bd79

The list 0, b, 0, b, …, b, 0 (m copies of b).
-/

/-- The list `0, b, 0, b, …, b, 0` (`m` copies of `b`). -/
def team_T2 (b : ℝ) : ℕ → List ℝ := fun
  | 0 => [0]
  | m + 1 => 0 :: b :: team_T2 b m
