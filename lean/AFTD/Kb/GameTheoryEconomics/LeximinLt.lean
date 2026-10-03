import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LeximinProfile

/-!
# leximin_lt

Topic: fair_division   Node: 2566cedd0b4f

y is strictly leximin-better than x: the sorted profile of x is lexicographically smaller than that of y.
-/

/-- `y` is strictly leximin-better than `x`: the sorted profile of `x` is lexicographically smaller. -/
def leximin_lt {n : ℕ} (x y : Fin n → ℝ) : Prop :=
  List.Lex (· < ·) (leximin_profile x) (leximin_profile y)
