import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanAvoidsAp
import AFTD.Kb.Tcs.EuclideanAvoidsApOfLe
import AFTD.Kb.Tcs.EuclideanHasMonoAp
import AFTD.Kb.Tcs.Op1481AvoidanceThreeTwentyOneDimOne

/-!
# op_1482_avoidance_three_seventeen_dim_one

Topic: combinatorics   Node: de5771e91225

Provenance: original. Related work: arXiv:2611.12360

There exists a two-coloring of 1-dimensional Euclidean space containing neither a monochromatic 3-term arithmetic progression with unit spacing of color false nor a monochromatic 17-term arithmetic progression with unit spacing of color true.
-/

noncomputable def op_1482_avoidance_three_seventeen_dim_one_c_parity
    (x : EuclideanSpace ℝ (Fin 1)) : Bool :=
  decide (Even ⌊x.ofLp 0⌋)

lemma op_1482_avoidance_three_seventeen_dim_one_not_mono_two (b : Bool) :
    ¬ euclidean_has_mono_ap op_1482_avoidance_three_seventeen_dim_one_c_parity 2 1 b := by
  intro ⟨x₀, v, hv, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  simp at h0 h1
  change decide (Even ⌊x₀.ofLp 0⌋) = b at h0
  change decide (Even ⌊x₀.ofLp 0 + v.ofLp 0⌋) = b at h1
  have heq : decide (Even ⌊x₀.ofLp 0 + v.ofLp 0⌋) = decide (Even ⌊x₀.ofLp 0⌋) := by
    rw [h1, h0]
  have hiff := op_1481_avoidance_three_twenty_one_dim_one_decide_even _ _ heq
  have hnorm : ‖v‖ = |v.ofLp 0| := op_1481_avoidance_three_twenty_one_dim_one_norm_eq_abs_coord v
  have habs : |v.ofLp 0| = 1 := by rw [← hnorm, hv]
  have hne := op_1481_avoidance_three_twenty_one_dim_one_floor_parity_ne_of_abs_one (x₀.ofLp 0) (v.ofLp 0) habs
  exact hne hiff

/-- In dimension 1, there exists a two-coloring of Euclidean space avoiding monochromatic 3-APs and 17-APs with unit spacing. -/
theorem op_1482_avoidance_three_seventeen_dim_one : euclidean_avoids_ap 1 3 1 17 1 := by
  apply euclidean_avoids_ap_of_le (r₁ := 2) (M₁ := 2) (by norm_num) (by norm_num)
  exact ⟨op_1482_avoidance_three_seventeen_dim_one_c_parity,
    op_1482_avoidance_three_seventeen_dim_one_not_mono_two false,
    op_1482_avoidance_three_seventeen_dim_one_not_mono_two true⟩
