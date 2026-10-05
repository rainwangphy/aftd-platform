import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.GpaUStar
import AFTD.Kb.GameTheoryEconomics.GpaCost
import AFTD.Kb.GameTheoryEconomics.GpaSimplex

/-!
# gpa_lhsSet

Topic: mechanism_design   Node: 5f903d4e4d6c

The set of values u*(σ) - h(σ) over the simplex (left side of Eq. (5.4)).
-/

/-- The set of values `u*(σ) - h(σ)` over the simplex (left side of Eq. (5.4)). -/
def gpa_lhsSet {k : ℕ} (e : Fin k → Fin k → ℝ) : Set ℝ :=
  (fun σ => gpa_uStar e σ - gpa_cost σ) '' gpa_simplex k
