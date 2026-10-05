import AFTD.Prelude

/-!
# team_T

Topic: algorithms   Node: a182d94fa045

The list 0, 1, 0, 1, …, 1, 0 (m ones, m+1 zeros).
-/

/-- The list `0, 1, 0, 1, …, 1, 0` (`m` ones, `m+1` zeros). -/
def team_T : ℕ → List ℝ := fun
  | 0 => [0]
  | m + 1 => 0 :: 1 :: team_T m
