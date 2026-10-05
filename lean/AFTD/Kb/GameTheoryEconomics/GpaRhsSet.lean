import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCube

/-!
# gpa_rhsSet

Topic: mechanism_design   Node: aa303ccdf999

The set of values u*(x) over the cube (right side of Eq. (5.4), before dividing by k).
-/

/-- The set of values `u*(x)` over the cube (right side of Eq. (5.4), before dividing by `k`). -/
def gpa_rhsSet {k : ℕ} (e : Fin k → Fin k → ℝ) : Set ℝ :=
  gpa_uStar e '' gpa_cube k
