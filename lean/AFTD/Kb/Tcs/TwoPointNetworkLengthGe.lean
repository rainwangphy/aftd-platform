import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# two_point_network_length_ge

Topic: approximation   Node: 1b52fab883a3

Provenance: helper lemma. Helper for cable_steiner_opt_two_points (sanity check of cable_steiner_opt).

If finitely many segments together with two points P, Q form a connected set, their total length is at least dist(P, Q).
-/

theorem two_point_network_length_ge (P Q : EuclideanSpace ℝ (Fin 2))
    (T : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)))
    (h : IsConnected (({P, Q} : Set (EuclideanSpace ℝ (Fin 2))) ∪ ⋃ t ∈ T, segment ℝ t.1 t.2)) :
    dist P Q ≤ ∑ t ∈ T, dist t.1 t.2 := by
  rcases eq_or_ne P Q with rfl | hPQ
  · simpa using Finset.sum_nonneg fun t _ => (dist_nonneg : 0 ≤ dist t.1 t.2)
  set v := Q - P with hv
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hPQ.symm)
  let φ : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ := innerSL ℝ v
  set X := (({P, Q} : Set (EuclideanSpace ℝ (Fin 2))) ∪ ⋃ t ∈ T, segment ℝ t.1 t.2) with hX
  have hφP : φ P ∈ φ '' X := ⟨P, by simp [hX], rfl⟩
  have hφQ : φ Q ∈ φ '' X := ⟨Q, by simp [hX], rfl⟩
  have hIcc : Set.Icc (φ P) (φ Q) ⊆ φ '' X :=
    (h.isPreconnected.image _ φ.continuous.continuousOn).Icc_subset hφP hφQ
  have himg : φ '' X ⊆ {φ P, φ Q} ∪ ⋃ t ∈ T, segment ℝ (φ t.1) (φ t.2) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases hx with hx | hx
    · rcases hx with rfl | rfl <;> simp
    · simp only [Set.mem_iUnion] at hx
      obtain ⟨t, ht, hxt⟩ := hx
      right
      simp only [Set.mem_iUnion]
      refine ⟨t, ht, ?_⟩
      have hs := image_segment ℝ ((φ : EuclideanSpace ℝ (Fin 2) →ₗ[ℝ] ℝ).toAffineMap) t.1 t.2
      simp only [LinearMap.coe_toAffineMap, ContinuousLinearMap.coe_coe] at hs
      rw [← hs]
      exact ⟨x, hxt, rfl⟩
  have hdiff : φ Q - φ P = ‖v‖ ^ 2 := by
    simp only [φ, innerSL_apply_apply, ← inner_sub_right, ← hv, real_inner_self_eq_norm_sq]
  have hseg : ∀ t ∈ T, MeasureTheory.volume (segment ℝ (φ t.1) (φ t.2)) ≤
      ENNReal.ofReal (dist t.1 t.2 * ‖v‖) := by
    intro t _
    rw [segment_eq_uIcc, Real.volume_interval]
    apply ENNReal.ofReal_le_ofReal
    have : φ t.2 - φ t.1 = inner ℝ v (t.2 - t.1) := by
      simp [φ, inner_sub_right]
    rw [this, dist_comm, dist_eq_norm, mul_comm]
    exact (abs_real_inner_le_norm v _).trans (by rw [mul_comm])
  have key : ENNReal.ofReal (‖v‖ ^ 2) ≤ ENNReal.ofReal (∑ t ∈ T, dist t.1 t.2 * ‖v‖) := by
    calc ENNReal.ofReal (‖v‖ ^ 2) = MeasureTheory.volume (Set.Icc (φ P) (φ Q)) := by
          rw [Real.volume_Icc, hdiff]
      _ ≤ MeasureTheory.volume ({φ P, φ Q} ∪ ⋃ t ∈ T, segment ℝ (φ t.1) (φ t.2)) :=
          MeasureTheory.measure_mono (hIcc.trans himg)
      _ ≤ MeasureTheory.volume ({φ P, φ Q} : Set ℝ) + MeasureTheory.volume (⋃ t ∈ T, segment ℝ (φ t.1) (φ t.2)) :=
          MeasureTheory.measure_union_le _ _
      _ = MeasureTheory.volume (⋃ t ∈ T, segment ℝ (φ t.1) (φ t.2)) := by
          rw [(Set.toFinite _).measure_zero, zero_add]
      _ ≤ ∑ t ∈ T, MeasureTheory.volume (segment ℝ (φ t.1) (φ t.2)) := MeasureTheory.measure_biUnion_finset_le _ _
      _ ≤ ∑ t ∈ T, ENNReal.ofReal (dist t.1 t.2 * ‖v‖) := Finset.sum_le_sum hseg
      _ = ENNReal.ofReal (∑ t ∈ T, dist t.1 t.2 * ‖v‖) :=
          (ENNReal.ofReal_sum_of_nonneg fun t _ => by positivity).symm
  rw [ENNReal.ofReal_le_ofReal_iff (Finset.sum_nonneg fun t _ => by positivity),
    ← Finset.sum_mul, sq] at key
  have h1 := le_of_mul_le_mul_right key hvpos
  rwa [dist_comm, dist_eq_norm]
