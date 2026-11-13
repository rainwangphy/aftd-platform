import AFTD.Prelude
import AFTD.Kb.Tcs.EuclideanHasMonoAp
import AFTD.Kb.Tcs.NormSqApQuadratic

/-!
# euclidean_radial_ap_avoidance_transfer_from_plane

Topic: combinatorics   Node: 0fec7c536fd0

Provenance: helper lemma. arXiv:2611.12360, Lemma 2.1, together with the Gram-matrix realization in the Euclidean plane

For a coloring determined solely by the squared distance from the origin, avoiding a monochromatic r-term arithmetic progression of spacing α and color b in the Euclidean plane implies avoidance of the same progression in every finite dimension. The same radial function is used in all dimensions.
-/

theorem euclidean_radial_ap_avoidance_transfer_from_plane (f : ℝ → Bool) (r n : ℕ) (α : ℝ) (b : Bool) (h : ¬ euclidean_has_mono_ap (fun x : EuclideanSpace ℝ (Fin 2) => f (‖x‖ ^ 2)) r α b) : ¬ euclidean_has_mono_ap (fun x : EuclideanSpace ℝ (Fin n) => f (‖x‖ ^ 2)) r α b := by
  rintro ⟨x₀, v, hvα, hcol⟩
  by_cases hv0 : v = 0
  · have ha0 : ‖v‖ = 0 := by rw [hv0]; simp
    let x₂ : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![‖x₀‖, 0]
    let v₂ : EuclideanSpace ℝ (Fin 2) := 0
    refine h ⟨x₂, v₂, ?_, ?_⟩
    · rw [show ‖v₂‖ = 0 from by simp [v₂], show α = 0 from hvα ▸ ha0]
    · intro k
      have hx₂ : ‖x₂‖ ^ 2 = ‖x₀‖ ^ 2 := by
        rw [EuclideanSpace.norm_sq_eq]
        simp [x₂, Fin.sum_univ_two]
      show f (‖x₂ + (k:ℝ) • v₂‖ ^ 2) = b
      rw [show x₂ + (k:ℝ) • v₂ = x₂ from by simp [v₂]]
      rw [hx₂]
      simpa [hv0] using hcol k
  · set a : ℝ := ‖v‖ with ha_eq
    set d : ℝ := ‖x₀‖ with hd_eq
    set c : ℝ := inner ℝ x₀ v with hc_eq
    have ha_pos : 0 < a := by
      rw [ha_eq]
      exact lt_of_le_of_ne (norm_nonneg v) (Ne.symm (norm_ne_zero_iff.mpr hv0))
    have hcs : c ^ 2 ≤ d ^ 2 * a ^ 2 := by
      have h1 : |c| ≤ d * a := by
        have := abs_real_inner_le_norm x₀ v
        rw [← hc_eq, ← hd_eq, ← ha_eq] at this
        exact this
      have h2 : |c| ^ 2 ≤ (d * a) ^ 2 := pow_le_pow_left₀ (abs_nonneg c) h1 2
      have h3 : (d * a) ^ 2 = d ^ 2 * a ^ 2 := by ring
      nlinarith [sq_abs c]
    set t : ℝ := c / a with ht_eq
    have ht_sq : t ^ 2 = c ^ 2 / a ^ 2 := by
      rw [ht_eq]; field_simp
    have hnonneg : 0 ≤ d ^ 2 - t ^ 2 := by
      have ha2 : (0:ℝ) < a ^ 2 := by positivity
      have ht2 : t ^ 2 * a ^ 2 = c ^ 2 := by
        rw [ht_sq]; field_simp
      nlinarith
    set s : ℝ := Real.sqrt (d ^ 2 - t ^ 2) with hs_eq
    have hs : s ^ 2 = d ^ 2 - t ^ 2 := by
      rw [hs_eq]; exact Real.sq_sqrt hnonneg
    let x₂ : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![t, s]
    let v₂ : EuclideanSpace ℝ (Fin 2) := (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![a, 0]
    have hv₂_sq : ‖v₂‖ ^ 2 = a ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [v₂, Fin.sum_univ_two]
    have hx₂_sq : ‖x₂‖ ^ 2 = d ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      simp [x₂, Fin.sum_univ_two]
      nlinarith [hs]
    have hin : inner ℝ x₂ v₂ = c := by
      rw [PiLp.inner_apply]
      simp [x₂, v₂, Fin.sum_univ_two]
      rw [ht_eq]; field_simp
    have hv2_norm : ‖v₂‖ = α := by
      have ha : ‖v₂‖ = a := by
        apply (sq_eq_sq₀ (norm_nonneg _) (le_of_lt ha_pos)).mp
        rw [hv₂_sq, ha_eq]
      rw [ha]; exact hvα
    refine h ⟨x₂, v₂, hv2_norm, ?_⟩
    intro k
    have heq : ‖x₂ + (k:ℝ) • v₂‖ ^ 2 = ‖x₀ + (k:ℝ) • v‖ ^ 2 := by
      rw [norm_sq_ap_quadratic x₂ v₂ (k:ℝ), norm_sq_ap_quadratic x₀ v (k:ℝ)]
      rw [hv₂_sq, hin, hx₂_sq, ← ha_eq, ← hc_eq, ← hd_eq]
    show f (‖x₂ + (k:ℝ) • v₂‖ ^ 2) = b
    rw [heq]
    exact hcol k
