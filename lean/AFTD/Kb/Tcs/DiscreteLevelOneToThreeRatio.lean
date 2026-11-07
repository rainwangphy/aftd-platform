import AFTD.Prelude
import AFTD.Kb.Tcs.FourierCrossLevel
import AFTD.Kb.Tcs.FourierVariance
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# discrete_level_one_to_three_ratio

Topic: combinatorics   Node: 3b15ae565f8a

Provenance: formalization of a published result. Source: arXiv:2611.08289 equation (52), line 1157

The discrete level 1 to 3 ratio for functions $f, g : \{0,1\}^n \to \mathbb{R}$ is defined as $(-W_3[f,g])_+ / (W_1[f,g] \log(\sqrt{\mathrm{Var}(f)\mathrm{Var}(g)} / W_1[f,g]))$, where $(x)_+ = \max(x, 0)$.
-/

/-- The ratio (-W_3[f,g])_+ / (W_1[f,g] log(√(Var(f)Var(g)) / W_1[f,g])) in the discrete level 1 to 3 inequality. -/
noncomputable def discrete_level_one_to_three_ratio {n : ℕ} (f g : BooleanAnalysis.BooleanFunc n) : ℝ := max (-fourier_cross_level 3 f g) 0 /
    (fourier_cross_level 1 f g * Real.log (Real.sqrt (fourier_variance f * fourier_variance g) / fourier_cross_level 1 f g))
