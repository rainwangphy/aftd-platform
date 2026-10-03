import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PropensityBanzhafMeasure

/-!
# propensity_banzhaf_index

Topic: general_equilibrium   Node: 9ce90693e9c1

The p-propensity Banzhaf power index: the power measure normalised to sum to 1.
-/

/-- The `p`-propensity Banzhaf power index: the power measure normalised to sum to 1. -/
noncomputable def propensity_banzhaf_index {n : ℕ} (p q : ℝ) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  propensity_banzhaf_measure p q w i / ∑ j, propensity_banzhaf_measure p q w j
