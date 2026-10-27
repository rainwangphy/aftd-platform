import AFTD.Prelude

/-!
# redistribution_disk_to_halfplane

Topic: mechanism_design   Node: 6ac28e9477be

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

The explicit fractional-linear disk map z -> i*y*(1+z)/(1-z). For positive y it maps the open unit disk to the upper half-plane.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

noncomputable def redistribution_disk_to_halfplane (y : ℝ) (z : ℂ) : ℂ := (y : ℂ) * Complex.I * (1+z) / (1-z)
