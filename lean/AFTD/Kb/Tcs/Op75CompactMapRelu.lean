import AFTD.Prelude
import AFTD.Kb.Tcs.Op75CompactMap

/-!
# op75_compact_map_relu

Topic: np_completeness   Node: b3936c1a7806

Provenance: helper lemma. OP-75, arXiv:2610.06092, one-pass subset-sum construction; a helper toward interval verification.

On the unit interval the compact map is computed by the displayed nested rectified affine expression.
-/

lemma op75_compact_map_relu (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    op75_compact_map x = 1 - max (1-4*x + max (8*x-3 - max (8*x-6) 0) 0) 0 := by
  unfold op75_compact_map
  rcases le_total (4*x-3) 0 with h | h
  · rw [abs_of_nonpos h]
    simp only [min_def, max_def]
    split_ifs <;> linarith [hx.1, hx.2]
  · rw [abs_of_nonneg h]
    simp only [min_def, max_def]
    split_ifs <;> linarith [hx.1, hx.2]
