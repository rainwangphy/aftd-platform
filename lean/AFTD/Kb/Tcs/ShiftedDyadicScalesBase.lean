import AFTD.Prelude
import AFTD.Kb.Tcs.ShiftedDyadicScales

/-!
# shifted_dyadic_scales_base

Topic: online_algorithms   Node: 0a8823559328

Provenance: helper lemma. arXiv:2611.17090, Section 3.1, Eq. (1)

For any phase θ ∈ ℝ, 2^θ is an element of the shifted dyadic scales R_θ.
-/

/-- The base scale 2^θ belongs to R_θ. -/
lemma shifted_dyadic_scales_base (θ : ℝ) : (2 : ℝ) ^ θ ∈ shifted_dyadic_scales θ := by
  exact ⟨0, by simp⟩
