import AFTD.Prelude
import AFTD.Tactic.NumBounds

/-!
# nae_sin_small_square

Topic: quantum   Node: 78d18826683e

Provenance: helper lemma. arXiv:1211.0721, Section 3.3, p-computation rule analysis

For real u with 0 ≤ u ≤ π/12, sin²(u) ≤ 1/14.
-/

theorem nae_sin_small_square (u : ℝ) (hu0 : 0 ≤ u) (hu : u ≤ Real.pi / 12) :
    Real.sin u ^ 2 ≤ (1 / 14 : ℝ) := by
  have hπ : Real.pi < (22 / 7 : ℝ) := by num_ineq
  have hsin0 : 0 ≤ Real.sin u :=
    Real.sin_nonneg_of_nonneg_of_le_pi hu0 (by linarith [Real.pi_pos])
  have hs : Real.sin u ≤ u := Real.sin_le hu0
  have hsle : Real.sin u ≤ (11 / 42 : ℝ) := by linarith
  have hsq : Real.sin u ^ 2 ≤ (11 / 42 : ℝ) ^ 2 :=
    (sq_le_sq₀ hsin0 (by norm_num)).mpr hsle
  nlinarith
