import AFTD.Prelude

/-!
# persuasion_marginal

Topic: mechanism_design   Node: 57b659f6dc0b

The marginal p_i(μ) = Pr_μ[X_i = 1].
-/

open Finset in
/-- The marginal `p_i(μ) = Pr_μ[X_i = 1]`. -/
noncomputable def persuasion_marginal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : (ι → Bool) → ℝ) (i : ι) : ℝ :=
  ∑ x, if x i = true then μ x else 0
