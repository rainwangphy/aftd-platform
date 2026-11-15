import AFTD.Prelude
import AFTD.Kb.Tcs.OseTwoLayerDirectEmbedding
import AFTD.Kb.Tcs.EmbedsIntoHilbertWithDistortion
import AFTD.Kb.Tcs.OseSphericalShrinkScalarBounds
import AFTD.Kb.Tcs.OseSphereTwoScaleDistanceIdentity
import AFTD.Kb.Tcs.OseSphericalSmallScaleAux

/-!
# ose_spherical_two_layer_hilbert_distortion_upper

Topic: algorithms   Node: bb9ca0564d70

Provenance: original. Related work: arXiv:2611.08546, Section 6.1, and one_strongly_euclidean_spherical_core_extension

Let a family of points in a complete real inner-product space lie on a sphere of radius q/2, with q positive and q² at least two, and have mutual distances at least one. Give two copies any metric whose first-layer distances are the original distances, whose cross-layer squared distances equal r² plus the original squared distances, and whose second-layer distances equal the minimum of s times the squared original distance and the original distance. If r,s are positive and s²+2rs=1, the whole two-layer metric embeds in Hilbert space with distortion at most min(q,1/s).
-/

theorem ose_spherical_two_layer_hilbert_distortion_upper (A H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H] (u : A → H) (c : H) (q r s : ℝ) (hq : 0 < q) (hq2 : 2 ≤ q ^ 2) (hr : 0 < r) (hs : 0 < s) (hid : s ^ 2 + 2 * r * s = 1) (hu : ∀ a, ‖u a - c‖ ^ 2 = q ^ 2 / 4) (hsep : ∀ a b, a ≠ b → 1 ≤ dist (u a) (u b)) (M : MetricSpace (Bool × A)) : letI := M; (∀ a b, dist (false,a) (false,b) = dist (u a) (u b)) → (∀ a b, dist (false,a) (true,b)^2 = r^2 + dist (u a) (u b)^2) → (∀ a b, dist (true,a) (true,b) = min (s * dist (u a) (u b)^2) (dist (u a) (u b))) → EmbedsIntoHilbertWithDistortion (Bool × A) (min q (1 / s)) := by
  intro hf hc hb
  have hq1 : 1 ≤ q := by nlinarith
  have hs1 : s ≤ 1 := by nlinarith [mul_pos hr hs]
  have hnorm (a : A) : ‖u a-c‖ = q/2 := by
    have h := hu a
    have hn : 0 ≤ ‖u a-c‖ := norm_nonneg _
    nlinarith
  have hdiam (a b : A) : dist (u a) (u b) ≤ q := by
    have htri := dist_triangle (u a) c (u b)
    have h1 : dist (u a) c = q/2 := by rw [dist_eq_norm, hnorm]
    have h2 : dist c (u b) = q/2 := by rw [dist_comm, dist_eq_norm, hnorm]
    linarith
  by_cases hsmall : s*q ≤ 1
  · have hsc := ose_spherical_shrink_scalar_bounds q r s hq hq2 hr hs hid hsmall
    dsimp only at hsc
    rcases hsc with ⟨_, _, _, hβ1, hβq, hprod, hdiff, hparam⟩
    let β : ℝ := min q (1/(s*q))
    have ht : ∀ a b, dist (true,a) (true,b) = s * dist (u a) (u b)^2 := by
      intro a b
      rw [hb, min_eq_left]
      have hd0 : 0 ≤ dist (u a) (u b) := dist_nonneg
      have hdq := hdiam a b
      have hle : s * dist (u a) (u b) ≤ 1 := le_trans (mul_le_mul_of_nonneg_left hdq hs.le) hsmall
      have hp := mul_nonneg hd0 (sub_nonneg.mpr hle)
      nlinarith only [hp]
    have hidentity (x y : H) (hx : ‖x‖^2 = q^2/4) (hy : ‖y‖^2 = q^2/4) :
        ‖β • x-(s*q) • y‖^2 = (β-s*q)^2*q^2/4+(s*q)*β*‖x-y‖^2 :=
      ose_sphere_two_scale_distance_identity H x y (s*q) β q hx hy
    obtain ⟨F, hF⟩ := ose_spherical_small_scale_aux A H u c q r s β hq1 hr.le hs hsmall
      hβ1 hβq hprod hdiff hparam hu hsep hidentity M hf hc ht
    have hmin : min q (1/s) = q := min_eq_left ((le_div_iff₀ hs).2 (by nlinarith [hsmall]))
    rw [hmin]
    exact ⟨WithLp 2 (H × ℝ), inferInstance, inferInstance, inferInstance, F, hF⟩
  · have hB : ∀ a b, s * dist (u a) (u b) ≤ dist (true,a) (true,b) ∧
        dist (true,a) (true,b) ≤ dist (u a) (u b) := by
      intro a b
      rw [hb]
      refine ⟨le_min ?_ ?_, min_le_right _ _⟩
      · by_cases hab : a=b
        · subst b; simp
        · have hd := hsep a b hab
          have hd0 : 0 ≤ dist (u a) (u b) := dist_nonneg
          have hp := mul_nonneg hs.le (mul_nonneg hd0 (by linarith : 0 ≤ dist (u a) (u b)-1))
          nlinarith only [hp]
      · have hp := mul_nonneg (by linarith : 0 ≤ 1-s) (dist_nonneg (x := u a) (y := u b))
        nlinarith only [hp]
    obtain ⟨F,hF⟩ := ose_two_layer_direct_embedding A H u r s hs hs1 M hf hc hB
    have hmin : min q (1/s) = 1/s := min_eq_right ((div_le_iff₀ hs).2 (by nlinarith [hsmall]))
    rw [hmin]
    exact ⟨WithLp 2 (H × ℝ), inferInstance, inferInstance, inferInstance, F, hF⟩
