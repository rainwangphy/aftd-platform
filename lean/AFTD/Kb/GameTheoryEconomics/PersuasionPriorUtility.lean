import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PersuasionMarginal

/-!
# persuasion_prior_utility

Topic: mechanism_design   Node: d8e35b5afead

The receiver's prior-only utility R_0(μ) = ∑_i max(p_i, 1 - p_i).
-/

open Finset in
/-- The receiver's prior-only utility `R_0(μ) = ∑_i max(p_i, 1 - p_i)`. -/
noncomputable def persuasion_prior_utility {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) : ℝ :=
  ∑ i, max (persuasion_marginal μ i) (1 - persuasion_marginal μ i)
