import AFTD.Prelude

/-!
# ag_min_aux

Topic: equilibria   Node: add4629c37fd

For rationals X, Y, the difference min(X,2) - min(Y,2) lies between 0 and X - Y.
-/

theorem ag_min_aux (X Y : ℚ) :
    (0 ≤ min X 2 - min Y 2 ∧ min X 2 - min Y 2 ≤ X - Y) ∨
      (X - Y ≤ min X 2 - min Y 2 ∧ min X 2 - min Y 2 ≤ 0) := by
  rcases le_total Y X with h | h
  · left
    constructor
    · have := min_le_min_right 2 h; linarith
    · simp only [min_def]; split_ifs <;> linarith
  · right
    constructor
    · simp only [min_def]; split_ifs <;> linarith
    · have := min_le_min_right 2 h; linarith
