import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplane
import AFTD.Kb.GameTheoryEconomics.RedistributionDiskToHalfplaneIm

/-!
# redistribution_disk_to_halfplane_im_pos

Topic: mechanism_design   Node: a754b8ef670e

Provenance: helper lemma. Uniform helper for IN-251, the proof of arXiv:2610.10995 Lemmas4.2/4.3. The disk logarithmic mean theorem and logarithm series already exist in the installed Mathlib; the upper-half-plane boundary passage, singular cosine integral and main harmonic bound remain unresolved. No research advance.

For positive y, every point of the open unit disk has a disk-map image of strictly positive imaginary part.
-/

open Finset Real MeasureTheory Metric MeromorphicOn

theorem redistribution_disk_to_halfplane_im_pos
    (y : ℝ) (hy : 0 < y) (z : ℂ) (hz : ‖z‖ < 1) :
    0 < (redistribution_disk_to_halfplane y z).im := by
  rw [redistribution_disk_to_halfplane_im]
  have hz1 : z ≠ 1 := by
    intro he
    rw [he, norm_one] at hz
    linarith
  have hsq : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]
    nlinarith [norm_nonneg z]
  apply div_pos (mul_pos hy (sub_pos.mpr hsq))
  exact Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hz1))
