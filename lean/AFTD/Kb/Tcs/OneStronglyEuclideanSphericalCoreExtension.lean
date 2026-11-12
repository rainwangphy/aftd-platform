import AFTD.Prelude
import AFTD.Kb.Tcs.OneStronglyEuclideanSphereExtensionScalarBounds
import AFTD.Kb.Tcs.OneStronglyEuclideanSphereRadialBound

/-!
# one_strongly_euclidean_spherical_core_extension

Topic: algorithms   Node: d35ee87c8974

Provenance: original. Related work: arXiv:2611.08546, Section 6.2, whose two-layer cube is a special case.

Let a family of points in a real inner-product space lie on a sphere of radius q/2, with q at least 1 and pairwise distances at least 1. Let r and s be positive with s²+2rs=1. Give two copies of the family any metric in which first-layer distances are the original distances and cross-layer squared distances are r² plus the corresponding original squared distances. The first-layer map extends to the entire two-layer metric with Lipschitz constant at most max(1,q/(2r+sq)).
-/

theorem one_strongly_euclidean_spherical_core_extension (A H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : A → H) (c : H) (q r s : ℝ)
    (hq : 1 ≤ q) (hr : 0 < r) (hs : 0 < s) (hid : s^2 + 2*r*s = 1)
    (hu : ∀ a, ‖u a - c‖^2 = q^2 / 4)
    (hsep : ∀ a b, a ≠ b → 1 ≤ dist (u a) (u b)^2)
    (M : MetricSpace (Bool × A)) :
    letI := M
    (∀ a b, dist (false,a) (false,b) = dist (u a) (u b)) →
    (∀ a b, dist (false,a) (true,b)^2 = r^2 + dist (u a) (u b)^2) →
    ∃ F : (Bool × A) → H,
      (∀ a, F (false,a) = u a) ∧
      ∀ x y, dist (F x) (F y) ≤ max 1 (q / (2*r + s*q)) * dist x y := by
  intro hfalse hcross
  let L := q / (2*r + s*q)
  let t := s * L
  have hpos_denom : 0 < 2*r + s*q := by positivity
  have hq_pos : 0 ≤ q := by linarith
  have hL : 0 ≤ L := div_nonneg hq_pos (le_of_lt hpos_denom)
  have hLdef : L * (2*r + s*q) = q := div_mul_cancel₀ q (ne_of_gt hpos_denom)
  have ht_nonneg : 0 ≤ t := mul_nonneg (le_of_lt hs) hL
  have hscal := one_strongly_euclidean_sphere_extension_scalar_bounds r s q L hr hs hq hid hL hLdef
  let F : Bool × A → H := fun (b, a) =>
    if b = false then u a else c + t • (u a - c)
  use F
  have hF_false : ∀ a, F (false, a) = u a := by
    intro a; rfl
  have hF_true : ∀ a, F (true, a) = c + t • (u a - c) := by
    intro a; rfl
  refine ⟨hF_false, ?_⟩
  rintro ⟨_ | _, a⟩ ⟨_ | _, b⟩
  · -- false, false
    rw [hF_false, hF_false]
    calc dist (u a) (u b) = 1 * dist (u a) (u b) := (one_mul _).symm
      _ ≤ max 1 L * dist (u a) (u b) :=
        mul_le_mul_of_nonneg_right (le_max_left 1 L) dist_nonneg
      _ = max 1 (q / (2*r + s*q)) * dist (false, a) (false, b) := by rw [hfalse]
  · -- false, true
    rw [hF_false, hF_true]
    let va := u a - c
    let vb := u b - c
    have hdiff : u a - (c + t • (u b - c)) = va - t • vb := by
      dsimp [va, vb]; rw [sub_add_eq_sub_sub]
    have hdist : dist (u a) (c + t • (u b - c)) = ‖va - t • vb‖ := by
      rw [dist_eq_norm, hdiff]
    have h_va : ‖va‖^2 = q^2 / 4 := hu a
    have h_vb : ‖vb‖^2 = q^2 / 4 := hu b
    have h_sub : ‖va - vb‖^2 = dist (u a) (u b)^2 := by
      rw [← dist_eq_norm, show va = u a - c by rfl, show vb = u b - c by rfl, dist_sub_right]
    have h2inner : 2 * inner ℝ va vb = ‖va‖^2 + ‖vb‖^2 - ‖va - vb‖^2 := by
      have h := norm_sub_sq_real va vb
      linarith
    have hnorm_sq : ‖va - t • vb‖^2 = ‖va‖^2 - t * (2 * inner ℝ va vb) + t^2 * ‖vb‖^2 := by
      have h := norm_sub_sq_real va (t • vb)
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
      linarith
    have h_alg : ‖va - t • vb‖^2 = q^2 * (1 - t)^2 / 4 + t * dist (u a) (u b)^2 := by
      nlinarith [h_va, h_vb, h_sub, h2inner, hnorm_sq]
    have h_le : ‖va - t • vb‖^2 ≤ L^2 * dist (false, a) (true, b)^2 := by
      have : 0 ≤ dist (u a) (u b)^2 := sq_nonneg _
      nlinarith [h_alg, hscal.1, hscal.2.1, hcross a b]
    have hL_dist : dist (u a) (c + t • (u b - c)) ≤ L * dist (false, a) (true, b) := by
      rw [hdist]
      have hLd : 0 ≤ L * dist (false, a) (true, b) := mul_nonneg hL dist_nonneg
      have hnorm_nonneg : 0 ≤ ‖va - t • vb‖ := norm_nonneg _
      nlinarith
    calc dist (u a) (c + t • (u b - c))
      _ ≤ L * dist (false, a) (true, b) := hL_dist
      _ ≤ max 1 L * dist (false, a) (true, b) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 L) dist_nonneg
  · -- true, false
    rw [dist_comm (F (true, a)) (F (false, b)), dist_comm (true, a) (false, b)]
    rw [hF_false, hF_true]
    let va := u b - c
    let vb := u a - c
    have hdiff : u b - (c + t • (u a - c)) = va - t • vb := by
      dsimp [va, vb]; rw [sub_add_eq_sub_sub]
    have hdist : dist (u b) (c + t • (u a - c)) = ‖va - t • vb‖ := by
      rw [dist_eq_norm, hdiff]
    have h_va : ‖va‖^2 = q^2 / 4 := hu b
    have h_vb : ‖vb‖^2 = q^2 / 4 := hu a
    have h_sub : ‖va - vb‖^2 = dist (u b) (u a)^2 := by
      rw [← dist_eq_norm, show va = u b - c by rfl, show vb = u a - c by rfl, dist_sub_right]
    have h2inner : 2 * inner ℝ va vb = ‖va‖^2 + ‖vb‖^2 - ‖va - vb‖^2 := by
      have h := norm_sub_sq_real va vb
      linarith
    have hnorm_sq : ‖va - t • vb‖^2 = ‖va‖^2 - t * (2 * inner ℝ va vb) + t^2 * ‖vb‖^2 := by
      have h := norm_sub_sq_real va (t • vb)
      rw [real_inner_smul_right, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs] at h
      linarith
    have h_alg : ‖va - t • vb‖^2 = q^2 * (1 - t)^2 / 4 + t * dist (u b) (u a)^2 := by
      nlinarith [h_va, h_vb, h_sub, h2inner, hnorm_sq]
    have h_le : ‖va - t • vb‖^2 ≤ L^2 * dist (false, b) (true, a)^2 := by
      have : 0 ≤ dist (u b) (u a)^2 := sq_nonneg _
      nlinarith [h_alg, hscal.1, hscal.2.1, hcross b a]
    have hL_dist : dist (u b) (c + t • (u a - c)) ≤ L * dist (false, b) (true, a) := by
      rw [hdist]
      have hLd : 0 ≤ L * dist (false, b) (true, a) := mul_nonneg hL dist_nonneg
      have hnorm_nonneg : 0 ≤ ‖va - t • vb‖ := norm_nonneg _
      nlinarith
    calc dist (u b) (c + t • (u a - c))
      _ ≤ L * dist (false, b) (true, a) := hL_dist
      _ ≤ max 1 L * dist (false, b) (true, a) :=
        mul_le_mul_of_nonneg_right (le_max_right 1 L) dist_nonneg
  · -- true, true
    rw [hF_true, hF_true]
    have hdist_eq : dist (c + t • (u a - c)) (c + t • (u b - c)) = t * dist (u a) (u b) := by
      rw [dist_eq_norm, dist_eq_norm]
      have : (c + t • (u a - c)) - (c + t • (u b - c)) = t • (u a - u b) := by
        calc (c + t • (u a - c)) - (c + t • (u b - c))
          _ = t • (u a - c) - t • (u b - c) := by abel
          _ = t • ((u a - c) - (u b - c)) := (smul_sub t (u a - c) (u b - c)).symm
          _ = t • (u a - u b) := by rw [sub_sub_sub_cancel_right]
      rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht_nonneg]
    by_cases hab : a = b
    · rw [hab, dist_self, dist_self, mul_zero]
    · have hd_sq : 1 ≤ dist (u a) (u b)^2 := hsep a b hab
      have hd_pos : 0 ≤ dist (u a) (u b) := dist_nonneg
      have hd_one : 1 ≤ dist (u a) (u b) := by nlinarith
      have hrad := one_strongly_euclidean_sphere_radial_bound r s (dist (u a) (u b)) hr hs hid hd_one
      have htri : dist (false, a) (true, b) ≤ dist (false, a) (true, a) + dist (true, a) (true, b) :=
        dist_triangle (false, a) (true, a) (true, b)
      have haa : dist (false, a) (true, a) = r := by
        have h1 := hcross a a
        have h2 : dist (u a) (u a) = 0 := dist_self (u a)
        have hpos : 0 ≤ dist (false, a) (true, a) := dist_nonneg
        nlinarith
      have hab_cross : dist (false, a) (true, b) = Real.sqrt (r^2 + dist (u a) (u b)^2) := by
        have h2 := hcross a b
        rw [← h2, Real.sqrt_sq dist_nonneg]
      have hdiff : Real.sqrt (r^2 + dist (u a) (u b)^2) - r ≤ dist (true, a) (true, b) := by
        linarith [htri, haa, hab_cross]
      have hs_dist : s * dist (u a) (u b) ≤ dist (true, a) (true, b) := le_trans hrad hdiff
      rw [hdist_eq]
      calc t * dist (u a) (u b)
        _ = L * (s * dist (u a) (u b)) := by
          show s * L * dist (u a) (u b) = L * (s * dist (u a) (u b))
          ring
        _ ≤ L * dist (true, a) (true, b) := mul_le_mul_of_nonneg_left hs_dist hL
        _ ≤ max 1 L * dist (true, a) (true, b) :=
          mul_le_mul_of_nonneg_right (le_max_right 1 L) dist_nonneg
