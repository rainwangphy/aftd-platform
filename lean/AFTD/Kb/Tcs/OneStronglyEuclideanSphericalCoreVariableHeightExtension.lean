import AFTD.Prelude
import AFTD.Kb.Tcs.OneStronglyEuclideanSphereRadialBound
import AFTD.Kb.Tcs.OneStronglyEuclideanVariableHeightScalarBound
import AFTD.Kb.Tcs.OneStronglyEuclideanSphereSquaredDistanceIdentity

/-!
# one_strongly_euclidean_spherical_core_variable_height_extension

Topic: algorithms   Node: 36c0607a957e

Provenance: original. Related work: arXiv:2611.08546, Section 6.2: the cited cube has equal cross-layer heights; this allows arbitrary positive heights for any spherical Euclidean core.

Let A and B be types, H a real inner-product space, u:A→H, p:B→A, c∈H, q≥1, and h:B→ℝ with h(b)>0 for every b. Assume ‖u(a)−c‖²=q²/4 for every a, and dist(u(a),u(a′))²≥1 whenever a≠a′. Let M be any metric structure on the disjoint union A⊕B. Assume dist(inl(a),inl(a′))=dist(u(a),u(a′)) and dist(inl(a),inr(b))²=h(b)²+dist(u(a),u(p(b)))² for every a,a′,b. Then there exists F:A⊕B→H with F(inl(a))=u(a) for every a, and dist(F(x),F(y))≤2√q·dist(x,y) for every x,y in A⊕B.
-/

lemma one_strongly_euclidean_spherical_core_variable_height_extension_cross_scalar (q z : ℝ) (hq : 1 ≤ q) (hz : 0 ≤ z) :
    let D := q + 2 * z + 2 * z^2
    let t := q / D
    (1 - t)^2 * (q^2 / 4) ≤ q * z^2 ∧ t ≤ q := by
  intro D t
  have hD_pos : 0 < D := by
    dsimp [D]
    have : 0 ≤ 2 * z := by linarith
    have : 0 ≤ 2 * z^2 := by positivity
    linarith
  have ht_le : t ≤ 1 := by
    dsimp [t, D]
    rw [div_le_iff₀ hD_pos]
    have : 0 ≤ 2 * z := by linarith
    have : 0 ≤ 2 * z^2 := by positivity
    linarith
  have ht_q : t ≤ q := by linarith
  refine ⟨?_, ht_q⟩
  have h1 : 1 - t = (2 * z + 2 * z^2) / D := by
    dsimp [t]
    rw [← div_self (ne_of_gt hD_pos), ← sub_div]
    dsimp [D]
    ring
  have h2 : (1 - t)^2 * (q^2 / 4) = (q * z * (1 + z) / D)^2 := by
    rw [h1]
    ring
  rw [h2]
  have h_bound := one_strongly_euclidean_variable_height_scalar_bound q z hq hz
  have h_lin : q * (1 + z) ≤ Real.sqrt q * D := by
    have : q * (1 + z) ≤ q * (1 + 2 * z) := by nlinarith
    linarith [h_bound]
  have h_mul : q * z * (1 + z) ≤ (Real.sqrt q * z) * D := by
    calc q * z * (1 + z) = z * (q * (1 + z)) := by ring
      _ ≤ z * (Real.sqrt q * D) := mul_le_mul_of_nonneg_left h_lin hz
      _ = (Real.sqrt q * z) * D := by ring
  have h_div : q * z * (1 + z) / D ≤ Real.sqrt q * z := by
    rw [div_le_iff₀ hD_pos]
    exact h_mul
  have h_nonneg : 0 ≤ q * z * (1 + z) / D := by
    apply div_nonneg _ (le_of_lt hD_pos)
    have : 0 ≤ q := by linarith
    have : 0 ≤ 1 + z := by linarith
    positivity
  have h_sq : (q * z * (1 + z) / D)^2 ≤ (Real.sqrt q * z)^2 := by
    nlinarith [h_div, h_nonneg]
  have h_rt : (Real.sqrt q * z)^2 = q * z^2 := by
    have : 0 ≤ q := by linarith
    rw [mul_pow, Real.sq_sqrt this]
  linarith

lemma one_strongly_euclidean_spherical_core_variable_height_extension_diff_quotient (q a b : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    let D := fun z => q + 2 * z + 2 * z^2
    let t := fun z => q / D z
    (q / 2) * (t a - t b) ≤ Real.sqrt q * (b - a) := by
  intro D t
  have hb_nonneg : 0 ≤ b := le_trans (le_of_lt ha) hab
  have hDa_pos : 0 < D a := by
    dsimp [D]
    have : 0 ≤ 2 * a := by linarith
    have : 0 ≤ 2 * a^2 := by positivity
    linarith
  have hDb_pos : 0 < D b := by
    dsimp [D]
    have : 0 ≤ 2 * b := by linarith
    have : 0 ≤ 2 * b^2 := by positivity
    linarith
  have hDa_ge_q : q ≤ D a := by
    dsimp [D]
    have : 0 ≤ 2 * a := by linarith
    have : 0 ≤ 2 * a^2 := by positivity
    linarith
  have h_diff : D b - D a = 2 * (b - a) * (1 + a + b) := by
    dsimp [D]
    ring
  have h_sub : t a - t b = q * (D b - D a) / (D a * D b) := by
    dsimp [t]
    rw [div_sub_div _ _ (ne_of_gt hDa_pos) (ne_of_gt hDb_pos)]
    ring
  have h_mul : (q / 2) * (t a - t b) = (q^2 * (b - a) * (1 + a + b)) / (D a * D b) := by
    rw [h_sub, h_diff]
    ring
  have h_bound := one_strongly_euclidean_variable_height_scalar_bound q b hq hb_nonneg
  have h_lin : 1 + a + b ≤ 1 + 2 * b := by linarith
  have h_prod : q^2 * (b - a) * (1 + a + b) ≤ (Real.sqrt q * (b - a)) * (D a * D b) := by
    have h1 : q * (1 + a + b) ≤ q * (1 + 2 * b) := by nlinarith
    have h2 : q * (1 + a + b) ≤ Real.sqrt q * D b := le_trans h1 h_bound
    have h3 : q * (b - a) * (q * (1 + a + b)) ≤ q * (b - a) * (Real.sqrt q * D b) :=
      mul_le_mul_of_nonneg_left h2 (by nlinarith)
    have h4 : q * (b - a) * (Real.sqrt q * D b) ≤ (Real.sqrt q * (b - a)) * (D a * D b) := by
      calc q * (b - a) * (Real.sqrt q * D b) = (Real.sqrt q * (b - a)) * (q * D b) := by ring
        _ ≤ (Real.sqrt q * (b - a)) * (D a * D b) := by
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hDa_ge_q (le_of_lt hDb_pos)
          · have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
            positivity
    calc q^2 * (b - a) * (1 + a + b) = q * (b - a) * (q * (1 + a + b)) := by ring
      _ ≤ (Real.sqrt q * (b - a)) * (D a * D b) := le_trans h3 h4
  rw [h_mul]
  rw [div_le_iff₀]
  · exact h_prod
  · positivity

lemma one_strongly_euclidean_spherical_core_variable_height_extension_radial_s (b : ℝ) (hb : 0 < b) :
    let s := Real.sqrt (b^2 + 1) - b
    0 < s ∧ s^2 + 2 * b * s = 1 ∧ 1 ≤ s * (1 + 2 * b) := by
  intro s
  have hb2 : 0 < b^2 + 1 := by positivity
  have hsq_rt : (Real.sqrt (b^2 + 1))^2 = b^2 + 1 := Real.sq_sqrt (le_of_lt hb2)
  have hrt_gt_b : b < Real.sqrt (b^2 + 1) := by
    have h1 : b^2 < b^2 + 1 := by linarith
    have h2 := Real.sqrt_lt_sqrt (sq_nonneg b) h1
    rwa [Real.sqrt_sq (le_of_lt hb)] at h2
  have hs_pos : 0 < s := by
    dsimp [s]; linarith
  have h_id : s^2 + 2 * b * s = 1 := by
    dsimp [s]
    have : (Real.sqrt (b^2 + 1) - b)^2 + 2 * b * (Real.sqrt (b^2 + 1) - b) =
      (Real.sqrt (b^2 + 1))^2 - b^2 := by ring
    rw [this, hsq_rt]
    ring
  have h_prod : s * (Real.sqrt (b^2 + 1) + b) = 1 := by
    dsimp [s]
    have : (Real.sqrt (b^2 + 1) - b) * (Real.sqrt (b^2 + 1) + b) =
      (Real.sqrt (b^2 + 1))^2 - b^2 := by ring
    rw [this, hsq_rt]
    ring
  have h_le : 1 ≤ s * (1 + 2 * b) := by
    have h_sqrt_le : Real.sqrt (b^2 + 1) ≤ b + 1 := by
      have h2 : 0 ≤ b + 1 := by linarith
      have h3 : b^2 + 1 ≤ (b + 1)^2 := by nlinarith
      rw [← Real.sqrt_sq h2]
      exact Real.sqrt_le_sqrt h3
    rw [← h_prod]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hs_pos)
    linarith
  exact ⟨hs_pos, h_id, h_le⟩

lemma one_strongly_euclidean_spherical_core_variable_height_extension_radial_prod (q b d Δ s : ℝ)
    (hq : 1 ≤ q) (hb : 0 < b) (hd : 0 ≤ d) (hs : 0 ≤ s)
    (h_sd : s * d ≤ Δ)
    (h_s_le : 1 ≤ s * (1 + 2 * b)) :
    let D := q + 2 * b + 2 * b^2
    let t := q / D
    t * d ≤ Real.sqrt q * Δ := by
  intro D t
  have h_scalar := one_strongly_euclidean_variable_height_scalar_bound q b hq (le_of_lt hb)
  have hD_pos : 0 < D := by
    dsimp [D]
    have : 0 ≤ 2 * b := by linarith
    have : 0 ≤ 2 * b^2 := by positivity
    linarith
  have h1 : t * d ≤ t * d * (s * (1 + 2 * b)) := by
    have ht_nonneg : 0 ≤ t := div_nonneg (by linarith) (le_of_lt hD_pos)
    have : 0 ≤ t * d := mul_nonneg ht_nonneg hd
    calc t * d = t * d * 1 := (mul_one _).symm
      _ ≤ t * d * (s * (1 + 2 * b)) := mul_le_mul_of_nonneg_left h_s_le this
  have h2 : t * d * (s * (1 + 2 * b)) = (t * (1 + 2 * b)) * (s * d) := by ring
  have h3 : t * (1 + 2 * b) ≤ Real.sqrt q := by
    dsimp [t]
    rw [div_mul_eq_mul_div, div_le_iff₀ hD_pos]
    exact h_scalar
  have h5 : (t * (1 + 2 * b)) * (s * d) ≤ Real.sqrt q * Δ :=
    mul_le_mul h3 h_sd (mul_nonneg hs hd) (Real.sqrt_nonneg q)
  linarith

lemma one_strongly_euclidean_spherical_core_variable_height_extension_dist_inr_ge (A B : Type) (M : MetricSpace (Sum A B))
    (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : A → H) (p : B → A) (h : B → ℝ)
    (hh : ∀ b, 0 < h b)
    (hcross : ∀ a b, (dist (Sum.inl a : Sum A B) (Sum.inr b))^2 = (h b)^2 + (dist (u a) (u (p b)))^2)
    (b1 b2 : B) :
    letI := M
    let d := dist (u (p b1)) (u (p b2))
    Real.sqrt ((h b2)^2 + d^2) - h b1 ≤ dist (Sum.inr b1 : Sum A B) (Sum.inr b2) := by
  intro d
  have h1 : dist (Sum.inl (p b1) : Sum A B) (Sum.inr b1) = h b1 := by
    have hsq := hcross (p b1) b1
    rw [dist_self, zero_pow two_ne_zero, add_zero] at hsq
    have h_nonneg : 0 ≤ dist (Sum.inl (p b1) : Sum A B) (Sum.inr b1) := dist_nonneg
    have hh_nonneg : 0 ≤ h b1 := le_of_lt (hh b1)
    nlinarith
  have h2 : dist (Sum.inl (p b1) : Sum A B) (Sum.inr b2) = Real.sqrt ((h b2)^2 + d^2) := by
    have hsq := hcross (p b1) b2
    have h_nonneg : 0 ≤ dist (Sum.inl (p b1) : Sum A B) (Sum.inr b2) := dist_nonneg
    rw [← hsq]
    exact (Real.sqrt_sq h_nonneg).symm
  have htri : dist (Sum.inl (p b1) : Sum A B) (Sum.inr b2) ≤
    dist (Sum.inl (p b1)) (Sum.inr b1) + dist (Sum.inr b1) (Sum.inr b2) :=
    dist_triangle (Sum.inl (p b1)) (Sum.inr b1) (Sum.inr b2)
  linarith

lemma one_strongly_euclidean_spherical_core_variable_height_extension_norm_decomp (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (c : H) (v1 v2 : H) (t1 t2 q d : ℝ)
    (ht2 : 0 ≤ t2) (ht12 : t2 ≤ t1)
    (hv1 : ‖v1‖ = q / 2) (hsub : ‖v1 - v2‖ = d) :
    ‖(c + t1 • v1) - (c + t2 • v2)‖ ≤ (q / 2) * (t1 - t2) + t2 * d := by
  have h_id : (c + t1 • v1) - (c + t2 • v2) = (t1 - t2) • v1 + t2 • (v1 - v2) := by
    calc (c + t1 • v1) - (c + t2 • v2) = t1 • v1 - t2 • v2 := by abel
      _ = (t1 - t2) • v1 + t2 • (v1 - v2) := by
        rw [sub_smul, smul_sub]
        abel
  rw [h_id]
  have h_tri := norm_add_le ((t1 - t2) • v1) (t2 • (v1 - v2))
  rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : 0 ≤ t1 - t2), abs_of_nonneg ht2,
      hv1, hsub] at h_tri
  linarith

lemma one_strongly_euclidean_spherical_core_variable_height_extension_t_antitone (q a b : ℝ) (hq : 1 ≤ q) (ha : 0 < a) (hab : a ≤ b) :
    let D := fun z => q + 2 * z + 2 * z^2
    let t := fun z => q / D z
    t b ≤ t a := by
  intro D t
  have hDa_pos : 0 < D a := by
    dsimp [D]
    have : 0 ≤ 2 * a := by linarith
    have : 0 ≤ 2 * a^2 := by positivity
    linarith
  have h_le : D a ≤ D b := by
    dsimp [D]
    have : 2 * a ≤ 2 * b := by linarith
    have : 2 * a^2 ≤ 2 * b^2 := by nlinarith
    linarith
  dsimp [t]
  exact div_le_div_of_nonneg_left (by linarith) hDa_pos h_le

lemma one_strongly_euclidean_spherical_core_variable_height_extension_second_layer_le (A B H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : A → H) (p : B → A) (c : H) (q : ℝ) (h : B → ℝ)
    (hq : 1 ≤ q) (hh : ∀ b, 0 < h b)
    (hu : ∀ a, ‖u a - c‖^2 = q^2 / 4)
    (hsep : ∀ a a', a ≠ a' → 1 ≤ dist (u a) (u a')^2)
    (M : MetricSpace (Sum A B))
    (hcross : ∀ a b, dist (Sum.inl a) (Sum.inr b)^2 = (h b)^2 + dist (u a) (u (p b))^2)
    (b1 b2 : B) (hle : h b1 ≤ h b2) :
    letI := M
    let D := fun z => q + 2 * z + 2 * z^2
    let t := fun z => q / D z
    let F2 := fun b => c + t (h b) • (u (p b) - c)
    dist (F2 b1) (F2 b2) ≤ (2 * Real.sqrt q) * dist (Sum.inr b1 : Sum A B) (Sum.inr b2) := by
  intro D t F2
  let a := h b1
  let b := h b2
  let d := dist (u (p b1)) (u (p b2))
  let Δ := dist (Sum.inr b1 : Sum A B) (Sum.inr b2)
  have ha_pos : 0 < a := hh b1
  have hb_pos : 0 < b := hh b2
  have hd_nonneg : 0 ≤ d := dist_nonneg
  have hΔ_nonneg : 0 ≤ Δ := dist_nonneg
  have h_inr_ge := one_strongly_euclidean_spherical_core_variable_height_extension_dist_inr_ge A B M H u p h hh hcross b1 b2
  have hb_le_rt : b ≤ Real.sqrt (b^2 + d^2) := by
    have : b = Real.sqrt (b^2) := (Real.sqrt_sq (le_of_lt hb_pos)).symm
    nth_rw 1 [this]
    apply Real.sqrt_le_sqrt
    have : 0 ≤ d^2 := sq_nonneg d
    linarith
  have h_ba_le_Δ : b - a ≤ Δ := by linarith [h_inr_ge, hb_le_rt]
  have h_rt_b_le_Δ : Real.sqrt (b^2 + d^2) - b ≤ Δ := by linarith [h_inr_ge, hle]
  have ht_diff := one_strongly_euclidean_spherical_core_variable_height_extension_diff_quotient q a b hq ha_pos hle
  have ht_diff_Δ : (q / 2) * (t a - t b) ≤ Real.sqrt q * Δ := by
    have h1 : Real.sqrt q * (b - a) ≤ Real.sqrt q * Δ :=
      mul_le_mul_of_nonneg_left h_ba_le_Δ (Real.sqrt_nonneg q)
    linarith [ht_diff, h1]
  have ht_d_Δ : t b * d ≤ Real.sqrt q * Δ := by
    by_cases h_eq : p b1 = p b2
    · have : d = 0 := by
        dsimp [d]
        rw [h_eq, dist_self]
      rw [this, mul_zero]
      have : 0 ≤ Real.sqrt q * Δ := mul_nonneg (Real.sqrt_nonneg q) hΔ_nonneg
      linarith
    · have hd_sq : 1 ≤ dist (u (p b1)) (u (p b2))^2 := hsep (p b1) (p b2) h_eq
      have hd_one : 1 ≤ d := by nlinarith [hd_sq, hd_nonneg]
      have hs_prop := one_strongly_euclidean_spherical_core_variable_height_extension_radial_s b hb_pos
      let s := Real.sqrt (b^2 + 1) - b
      have hrad := one_strongly_euclidean_sphere_radial_bound b s d hb_pos hs_prop.1 hs_prop.2.1 hd_one
      have h_sd_le_Δ : s * d ≤ Δ := le_trans hrad h_rt_b_le_Δ
      exact one_strongly_euclidean_spherical_core_variable_height_extension_radial_prod q b d Δ s hq hb_pos hd_nonneg (le_of_lt hs_prop.1) h_sd_le_Δ hs_prop.2.2
  have h_norm1 : ‖u (p b1) - c‖ = q / 2 := by
    have hu1 := hu (p b1)
    have : 0 ≤ q / 2 := by linarith
    have : 0 ≤ ‖u (p b1) - c‖ := norm_nonneg _
    nlinarith
  have h_sub_d : ‖(u (p b1) - c) - (u (p b2) - c)‖ = d := by
    dsimp [d]
    rw [sub_sub_sub_cancel_right, dist_eq_norm]
  have ht_anti := one_strongly_euclidean_spherical_core_variable_height_extension_t_antitone q a b hq ha_pos hle
  have ht2_nonneg : 0 ≤ t b := by
    dsimp [t]
    have : 0 < q + 2 * b + 2 * b^2 := by
      have : 0 ≤ 2 * b := by linarith
      have : 0 ≤ 2 * b^2 := by positivity
      linarith
    exact div_nonneg (by linarith) (le_of_lt this)
  have h_decomp := one_strongly_euclidean_spherical_core_variable_height_extension_norm_decomp H c (u (p b1) - c) (u (p b2) - c) (t a) (t b) q d
    ht2_nonneg ht_anti h_norm1 h_sub_d
  dsimp [F2]
  rw [dist_eq_norm]
  linarith

theorem one_strongly_euclidean_spherical_core_variable_height_extension (A B H : Type) [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u : A → H) (p : B → A) (c : H) (q : ℝ) (h : B → ℝ)
    (hq : 1 ≤ q) (hh : ∀ b, 0 < h b)
    (hu : ∀ a, ‖u a - c‖^2 = q^2 / 4)
    (hsep : ∀ a a', a ≠ a' → 1 ≤ dist (u a) (u a')^2)
    (M : MetricSpace (Sum A B)) :
    letI := M
    (∀ a a', dist (Sum.inl a : Sum A B) (Sum.inl a') = dist (u a) (u a')) →
    (∀ a b, dist (Sum.inl a) (Sum.inr b)^2 = (h b)^2 + dist (u a) (u (p b))^2) →
    ∃ F : Sum A B → H,
      (∀ a, F (Sum.inl a) = u a) ∧
      ∀ x y, dist (F x) (F y) ≤ (2 * Real.sqrt q) * dist x y := by
  intro hinl hcross
  let D : ℝ → ℝ := fun z => q + 2 * z + 2 * z^2
  let t : ℝ → ℝ := fun z => q / D z
  let F : Sum A B → H := fun x =>
    match x with
    | Sum.inl a => u a
    | Sum.inr b => c + t (h b) • (u (p b) - c)
  use F
  refine ⟨fun a => rfl, ?_⟩
  rintro (a1 | b1) (a2 | b2)
  · -- inl a1, inl a2
    dsimp [F]
    have hq1 : 1 ≤ Real.sqrt q := Real.one_le_sqrt.mpr hq
    have h2q : 1 ≤ 2 * Real.sqrt q := by linarith
    have h_d : dist (u a1) (u a2) ≤ (2 * Real.sqrt q) * dist (u a1) (u a2) := by
      calc dist (u a1) (u a2) = 1 * dist (u a1) (u a2) := (one_mul _).symm
        _ ≤ (2 * Real.sqrt q) * dist (u a1) (u a2) :=
          mul_le_mul_of_nonneg_right h2q dist_nonneg
    rwa [hinl a1 a2]
  · -- inl a1, inr b2
    rw [dist_eq_norm]
    let x := u a1 - c
    let y := u (p b2) - c
    have h_diff : F (Sum.inl a1) - F (Sum.inr b2) = x - t (h b2) • y := by
      dsimp [F, x, y]
      abel
    rw [h_diff]
    have h_id := one_strongly_euclidean_sphere_squared_distance_identity H x y (t (h b2)) q (hu a1) (hu (p b2))
    have h_scal := one_strongly_euclidean_spherical_core_variable_height_extension_cross_scalar q (h b2) hq (le_of_lt (hh b2))
    have h_sq : ‖x - t (h b2) • y‖^2 ≤ q * dist (Sum.inl a1 : Sum A B) (Sum.inr b2)^2 := by
      rw [h_id, hcross a1 b2]
      have h_xy : ‖x - y‖^2 = dist (u a1) (u (p b2))^2 := by
        have : x - y = u a1 - u (p b2) := by dsimp [x, y]; abel
        rw [this, ← dist_eq_norm]
      rw [h_xy]
      have h1 := h_scal.1
      have h2 := h_scal.2
      have : 0 ≤ dist (u a1) (u (p b2))^2 := sq_nonneg _
      nlinarith
    have hq_pos : 0 ≤ q := by linarith
    have h_d_nonneg : 0 ≤ dist (Sum.inl a1 : Sum A B) (Sum.inr b2) := dist_nonneg
    have h_4q : q * dist (Sum.inl a1 : Sum A B) (Sum.inr b2)^2 ≤
        ((2 * Real.sqrt q) * dist (Sum.inl a1) (Sum.inr b2))^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hq_pos]
      nlinarith
    have h_norm_nonneg : 0 ≤ ‖x - t (h b2) • y‖ := norm_nonneg _
    have h_rhs_nonneg : 0 ≤ (2 * Real.sqrt q) * dist (Sum.inl a1 : Sum A B) (Sum.inr b2) := by
      have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
      positivity
    nlinarith
  · -- inr b1, inl a2
    rw [dist_comm (F (Sum.inr b1)) (F (Sum.inl a2)), dist_comm (Sum.inr b1 : Sum A B) (Sum.inl a2)]
    rw [dist_eq_norm]
    let x := u a2 - c
    let y := u (p b1) - c
    have h_diff : F (Sum.inl a2) - F (Sum.inr b1) = x - t (h b1) • y := by
      dsimp [F, x, y]
      abel
    rw [h_diff]
    have h_id := one_strongly_euclidean_sphere_squared_distance_identity H x y (t (h b1)) q (hu a2) (hu (p b1))
    have h_scal := one_strongly_euclidean_spherical_core_variable_height_extension_cross_scalar q (h b1) hq (le_of_lt (hh b1))
    have h_sq : ‖x - t (h b1) • y‖^2 ≤ q * dist (Sum.inl a2 : Sum A B) (Sum.inr b1)^2 := by
      rw [h_id, hcross a2 b1]
      have h_xy : ‖x - y‖^2 = dist (u a2) (u (p b1))^2 := by
        have : x - y = u a2 - u (p b1) := by dsimp [x, y]; abel
        rw [this, ← dist_eq_norm]
      rw [h_xy]
      have h1 := h_scal.1
      have h2 := h_scal.2
      have : 0 ≤ dist (u a2) (u (p b1))^2 := sq_nonneg _
      nlinarith
    have hq_pos : 0 ≤ q := by linarith
    have h_d_nonneg : 0 ≤ dist (Sum.inl a2 : Sum A B) (Sum.inr b1) := dist_nonneg
    have h_4q : q * dist (Sum.inl a2 : Sum A B) (Sum.inr b1)^2 ≤
        ((2 * Real.sqrt q) * dist (Sum.inl a2) (Sum.inr b1))^2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hq_pos]
      nlinarith
    have h_norm_nonneg : 0 ≤ ‖x - t (h b1) • y‖ := norm_nonneg _
    have h_rhs_nonneg : 0 ≤ (2 * Real.sqrt q) * dist (Sum.inl a2 : Sum A B) (Sum.inr b1) := by
      have : 0 ≤ Real.sqrt q := Real.sqrt_nonneg q
      positivity
    nlinarith
  · -- inr b1, inr b2
    rcases le_total (h b1) (h b2) with hle | hle
    · exact one_strongly_euclidean_spherical_core_variable_height_extension_second_layer_le A B H u p c q h hq hh hu hsep M hcross b1 b2 hle
    · rw [dist_comm (F (Sum.inr b1)) (F (Sum.inr b2)), dist_comm (Sum.inr b1 : Sum A B) (Sum.inr b2)]
      exact one_strongly_euclidean_spherical_core_variable_height_extension_second_layer_le A B H u p c q h hq hh hu hsep M hcross b2 b1 hle
