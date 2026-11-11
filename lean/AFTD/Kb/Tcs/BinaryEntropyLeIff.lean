import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryEntropy

/-!
# binaryEntropy_le_iff

Topic: information   Node: 1a9c00c0af85

Provenance: helper lemma. step towards inhomogeneous_dephased_path_mmi_local_noise_criterion

The binary entropy function is strictly increasing on [0, 1/2], so for any x, y in [0, 1/2], binaryEntropy x ≤ binaryEntropy y if and only if x ≤ y.
-/

/-- Monotonicity characterization of binary entropy on [0, 1/2]. -/
theorem binaryEntropy_le_iff {x y : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) (1 / 2)) (hy : y ∈ Set.Icc (0 : ℝ) (1 / 2)) :
    binaryEntropy x ≤ binaryEntropy y ↔ x ≤ y := by
  have hform (z : ℝ) : binaryEntropy z = Real.binEntropy z / Real.log 2 := by
    simp only [binaryEntropy, Real.binEntropy, Real.logb, Real.log_inv]
    ring
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstrict : StrictMonoOn binaryEntropy (Set.Icc (0 : ℝ) (1 / 2)) := by
    intro a ha b hb hab
    rw [hform, hform]
    exact (div_lt_div_iff_of_pos_right hp).2
      (Real.binEntropy_strictMonoOn (by simpa using ha) (by simpa using hb) hab)
  constructor
  · intro h
    by_contra hn
    exact (not_le_of_gt (hstrict hy hx (lt_of_not_ge hn))) h
  · exact hstrict.monotoneOn hx hy
