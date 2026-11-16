import AFTD.Prelude
import AFTD.Kb.Tcs.DownScale
import AFTD.Kb.Tcs.ShiftedDyadicScales

/-!
# down_scale_mem_shifted_dyadic_scales

Topic: online_algorithms   Node: ff6fa5d315b7

Provenance: helper lemma. arXiv:2611.17090, Section 3.1, Eq. (1)

For any phase θ and any positive real number z > 0, down_θ(z) belongs to R_θ.
-/

/-- Downward rounding of any positive real produces an element of R_θ. -/
lemma down_scale_mem_shifted_dyadic_scales (θ : ℝ) {z : ℝ} (hz : 0 < z) :
    down_scale θ z ∈ shifted_dyadic_scales θ := by
  dsimp [down_scale, shifted_dyadic_scales]
  split_ifs with h
  · linarith
  · exact ⟨⌊Real.logb 2 z - θ⌋, rfl⟩
