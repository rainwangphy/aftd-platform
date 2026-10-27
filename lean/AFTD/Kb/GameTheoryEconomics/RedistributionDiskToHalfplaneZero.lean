import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplane

/-!
# redistribution_disk_to_halfplane_zero

Topic: mechanism_design   Node: d0036637fc9b

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

The disk map sends zero to i*y for every real y.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_disk_to_halfplane_zero (y : ℝ) :
    redistribution_disk_to_halfplane y 0 = (y : ℂ) * Complex.I := by
  simp [redistribution_disk_to_halfplane]
