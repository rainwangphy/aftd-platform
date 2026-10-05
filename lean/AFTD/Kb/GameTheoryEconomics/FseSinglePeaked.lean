import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FseCost

/-!
# fse_SinglePeaked

Topic: mechanism_design   Node: 075adcc55160

The (weak) single-peakedness of the preference of an agent at x under scaling q: the cost does not decrease when the facility moves away from x on either side.
-/

/-- The (weak) single-peakedness of the preference of an agent at `x` under scaling `q`: the cost does not decrease when the facility moves away from `x` on either side. -/
def fse_SinglePeaked (q : ℝ → ℝ) (x : ℝ) : Prop :=
  ∀ y y' : ℝ, y ∈ Set.Icc (0 : ℝ) 1 → y' ∈ Set.Icc (0 : ℝ) 1 →
    ((x ≤ y ∧ y ≤ y') ∨ (y' ≤ y ∧ y ≤ x)) → fse_cost q y x ≤ fse_cost q y' x
