import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplane

/-!
# redistribution_disk_to_halfplane_im

Topic: mechanism_design   Node: d045e7218db7

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

The imaginary part of the disk map is y*(1-normSq(z))/normSq(1-z), including the totalized division convention at z=1.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_disk_to_halfplane_im (y : ℝ) (z : ℂ) :
    (redistribution_disk_to_halfplane y z).im =
      y * (1-Complex.normSq z) / Complex.normSq (1-z) := by
  simp [redistribution_disk_to_halfplane, Complex.div_im, Complex.normSq_apply]
  ring
