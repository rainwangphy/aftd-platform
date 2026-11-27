import AFTD.Prelude
import AFTD.Kb.Physics.GeometricGibbs
import AFTD.Kb.Physics.GeometricGibbsPrefixWeight
import AFTD.Kb.Optimization.RelativeLorenzCurve

/-!
# geometric_thermo_diff

Topic: quantum_mechanics   Node: c12375421fab

Provenance: formalization of a published result. Source: arXiv:2610.35433

For natural numbers N and j, real number q, and population vectors x and y on Fin N, the thermomajorization prefix difference geometric_thermo_diff N q x y j is relative_lorenz_curve y (geometric_gibbs N q) (geometric_gibbs_prefix_weight N q j) - relative_lorenz_curve x (geometric_gibbs N q) (geometric_gibbs_prefix_weight N q j).
-/

/-- Thermomajorization curve difference at prefix j. -/
noncomputable def geometric_thermo_diff (N : ℕ) (q : ℝ) (x y : Fin N → ℝ) (j : ℕ) : ℝ := relative_lorenz_curve y (geometric_gibbs N q) (geometric_gibbs_prefix_weight N q j) - relative_lorenz_curve x (geometric_gibbs N q) (geometric_gibbs_prefix_weight N q j)
