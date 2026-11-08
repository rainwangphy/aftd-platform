import AFTD.Prelude
import AFTD.Kb.Tcs.HasSubspaceCompatibleIncompatibleFamily
import AFTD.Kb.Tcs.RCLikeNormSqEqConjMulSelf

/-!
# subspace_incompatible_family_of_mic_data

Topic: quantum   Node: 2ce753a11a46

Provenance: helper lemma. arXiv:2610.37347 (Measurement incompatibility and noiseless quantum codes), proof of the main theorem (Eqs. 5-7) and Corollary 1

For all d k : ℕ, let g : Fin k → Fin d → ℂ, write G i = Matrix.vecMulVec (g i) (star (g i)) (the rank-one positive matrix g_i g_i^*), let c : Fin k → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ) be real-linear functionals, F : Matrix (Fin d) (Fin d) ℂ and i0 : Fin k. Suppose (1) ∑ i, G i = 1; (2) c i (G j) = if i = j then 1 else 0 for all i j; (3) every Hermitian X satisfies X = ∑ i, c i X • G i (real scalar multiplication); (4) F.IsHermitian and IsUnit F.det; (5) c i0 X = (F * X).trace.re for every Hermitian X; (6) there is a real s with 1 < s and (1 - s • G i0).PosSemidef. Then has_subspace_compatible_incompatible_family d k holds: a rank-one informationally complete measurement whose dual operator F for the outcome i0 is invertible yields k binary measurements that are incompatible on C^d but jointly measurable after compression to every proper subspace.
-/

open Matrix in
open scoped ComplexOrder in
theorem rank_one_psd_dominated_eq_smul {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) (v : Fin d → ℂ)
    (hA : A.PosSemidef) (hB : (vecMulVec v (star v) - A).PosSemidef) :
    ∃ a : ℝ, 0 ≤ a ∧ A = a • vecMulVec v (star v) := by
  have step1 : ∀ x : Fin d → ℂ, star v ⬝ᵥ x = 0 → A *ᵥ x = 0 := by
    intro x hx
    have h1 := hB.dotProduct_mulVec_nonneg x
    have h2 := hA.dotProduct_mulVec_nonneg x
    have hvx : vecMulVec v (star v) *ᵥ x = 0 := by
      ext i; simp [mulVec, vecMulVec, dotProduct, mul_assoc, ← Finset.mul_sum] at hx ⊢
      right; simpa [dotProduct] using hx
    rw [sub_mulVec, hvx, zero_sub, dotProduct_neg] at h1
    have : star x ⬝ᵥ (A *ᵥ x) = 0 := le_antisymm (by simpa using h1) h2
    exact (hA.dotProduct_mulVec_zero_iff x).mp this
  by_cases hv : v = 0
  · refine ⟨0, le_rfl, ?_⟩
    subst hv
    ext i j
    have := congrFun (step1 (Pi.single j 1) (by simp)) i
    simpa [mulVec_single_one] using this
  · obtain ⟨k, hk⟩ : ∃ k, v k ≠ 0 := by
      by_contra h; push Not at h; exact hv (funext h)
    have hcol : ∀ c a, A c a * star (v k) = A c k * star (v a) := by
      intro c a
      have hx : star v ⬝ᵥ (star (v k) • Pi.single a 1 - star (v a) • Pi.single k 1) = 0 := by
        simp [dotProduct_sub, dotProduct_smul]; ring
      have := congrFun (step1 _ hx) c
      simp [mulVec_sub, mulVec_smul] at this
      simp only [RCLike.star_def]
      linear_combination this
    have hH := hA.isHermitian
    have hkk : star (A k k) = A k k := by
      have := congrFun (congrFun hH k) k; simpa using this
    have hrow : ∀ c, A c k * v k = A k k * v c := by
      intro c
      have h := hcol k c
      have hc : A c k = star (A k c) := by
        have := congrFun (congrFun hH k) c; simp at this; rw [← this]; simp
      rw [hc]
      have := congrArg star h
      simp at this
      simp only [RCLike.star_def] at hkk ⊢
      rw [hkk] at this
      linear_combination this
    have hn : (Complex.normSq (v k) : ℂ) ≠ 0 := by
      simpa [Complex.normSq_eq_zero] using hk
    refine ⟨(A k k).re / Complex.normSq (v k), ?_, ?_⟩
    · apply div_nonneg _ (Complex.normSq_nonneg _)
      have := hA.diag_nonneg (i := k)
      exact (Complex.nonneg_iff.mp this).1
    · have hre : ((A k k).re : ℂ) = A k k := by
        have := hA.diag_nonneg (i := k)
        have h0 := (Complex.nonneg_iff.mp this).2
        apply Complex.ext <;> simp [h0]
      ext c a
      simp only [Matrix.smul_apply, vecMulVec_apply, Pi.star_apply, Complex.real_smul]
      push_cast
      rw [hre, Complex.normSq_eq_conj_mul_self]
      have e1 := hcol c a
      have e2 := hrow c
      have key : A c a * ((starRingEnd ℂ) (v k) * v k) = A k k * (v c * (starRingEnd ℂ) (v a)) := by
        simp only [RCLike.star_def] at *
        linear_combination (v k) * e1 + (starRingEnd ℂ) (v a) * e2
      have hn' : (starRingEnd ℂ) (v k) * v k ≠ 0 := by
        rw [← Complex.normSq_eq_conj_mul_self]; exact hn
      simp only [RCLike.star_def]
      rw [div_mul_eq_mul_div, eq_div_iff hn']
      exact key

open Matrix in
theorem real_linear_matrix_functional_entry_bound {d : ℕ} (l : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ)
    (X : Matrix (Fin d) (Fin d) ℂ) (K : ℝ) (hX : ∀ a b, ‖X a b‖ ≤ K) :
    |l X| ≤ (∑ a, ∑ b, (|l (single a b 1)| + |l (single a b Complex.I)|)) * K := by
  have hdec : X = ∑ a, ∑ b, ((X a b).re • single a b (1 : ℂ) + (X a b).im • single a b Complex.I) := by
    conv_lhs => rw [matrix_eq_sum_single X]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ext i j
    simp only [single_apply, Matrix.add_apply, Matrix.smul_apply]
    split_ifs
    · apply Complex.ext <;> simp
    · simp
  rw [hdec]
  simp only [map_sum, map_add, map_smul, smul_eq_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun b _ => ?_)
  have h1 : |(X a b).re| ≤ K := (Complex.abs_re_le_norm _).trans (hX a b)
  have h2 : |(X a b).im| ≤ K := (Complex.abs_im_le_norm _).trans (hX a b)
  calc |(X a b).re * l (single a b 1) + (X a b).im * l (single a b Complex.I)|
      ≤ |(X a b).re| * |l (single a b 1)| + |(X a b).im| * |l (single a b Complex.I)| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ K * |l (single a b 1)| + K * |l (single a b Complex.I)| := by
        gcongr
    _ = (|l (single a b 1)| + |l (single a b Complex.I)|) * K := by ring

open Matrix in
theorem hermitian_idempotent_entry_norm_le_trace_re {d : ℕ} (Q : Matrix (Fin d) (Fin d) ℂ) (hH : Q.IsHermitian)
    (hQ : Q * Q = Q) (a b : Fin d) : ‖Q a b‖ ≤ Q.trace.re := by
  have hent : ∀ x y, Q x y = star (Q y x) := by
    intro x y; have := congrFun (congrFun hH y) x; simp at this; rw [← this]; simp
  have hdiag : ∀ x, (Q x x).re = ∑ e, ‖Q x e‖ ^ 2 := by
    intro x
    have : Q x x = ∑ e, Q x e * Q e x := by
      conv_lhs => rw [← hQ]
      simp [mul_apply]
    rw [this, Complex.re_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [hent e x, RCLike.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]; norm_cast
  have hdiag' : ∀ x, (Q x x).re = ∑ e, ‖Q e x‖ ^ 2 := by
    intro x; rw [hdiag]; refine Finset.sum_congr rfl fun e _ => ?_
    rw [hent x e, norm_star]
  have hab : ‖Q a b‖ ≤ ((Q a a).re + (Q b b).re) / 2 := by
    have : Q a b = ∑ e, Q a e * Q e b := by
      conv_lhs => rw [← hQ]
      simp [mul_apply]
    rw [this, hdiag a, hdiag' b, ← Finset.sum_add_distrib, Finset.sum_div]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun e _ => ?_)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖Q a e‖ - ‖Q e b‖)]
  have hnn : ∀ x, 0 ≤ (Q x x).re := fun x => by rw [hdiag]; positivity
  have htr : ∀ x, (Q x x).re ≤ Q.trace.re := by
    intro x
    rw [trace, Complex.re_sum]
    exact Finset.single_le_sum (f := fun y => (Q y y).re) (fun y _ => hnn y) (Finset.mem_univ x)
  linarith [htr a, htr b]

open scoped ComplexOrder in
theorem subspace_incompatible_family_of_mic_data {d k : ℕ} (g : Fin k → Fin d → ℂ)
    (c : Fin k → (Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] ℝ)) (F : Matrix (Fin d) (Fin d) ℂ) (i0 : Fin k)
    (hsum : ∑ i, Matrix.vecMulVec (g i) (star (g i)) = 1)
    (hdual : ∀ i j, c i (Matrix.vecMulVec (g j) (star (g j))) = if i = j then 1 else 0)
    (hspan : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian →
      X = ∑ i, c i X • Matrix.vecMulVec (g i) (star (g i)))
    (hF : F.IsHermitian) (hFu : IsUnit F.det)
    (hc0 : ∀ X : Matrix (Fin d) (Fin d) ℂ, X.IsHermitian → c i0 X = (F * X).trace.re)
    (hs : ∃ s : ℝ, 1 < s ∧ (1 - s • Matrix.vecMulVec (g i0) (star (g i0))).PosSemidef) :
    has_subspace_compatible_incompatible_family d k := open Matrix in by
  classical
  set G : Fin k → Matrix (Fin d) (Fin d) ℂ := fun i => vecMulVec (g i) (star (g i)) with hGdef
  have hGpsd : ∀ i, (G i).PosSemidef := fun i => posSemidef_vecMulVec_self_star _
  have hsum' : ∑ i, G i = 1 := hsum
  obtain ⟨smax, hsmax, hsPSD⟩ := hs
  -- the linear maps
  set Yl : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ :=
    (1/2 : ℝ) • (LinearMap.mulLeft ℝ F⁻¹ + LinearMap.mulRight ℝ F⁻¹) with hYl
  have hYl_apply : ∀ X, Yl X = (1/2 : ℝ) • (F⁻¹ * X + X * F⁻¹) := by
    intro X; simp [hYl]
  set Cst : ℝ := 1 + ∑ i, ∑ a, ∑ b, (|((c i).comp Yl) (single a b 1)| +
      |((c i).comp Yl) (single a b Complex.I)|) with hCst
  have hC1 : 1 ≤ Cst := by
    have : 0 ≤ ∑ i, ∑ a, ∑ b, (|((c i).comp Yl) (single a b 1)| +
      |((c i).comp Yl) (single a b Complex.I)|) := by positivity
    linarith
  have hCpos : 0 < Cst := by linarith
  have hbound : ∀ i X (K : ℝ), 0 ≤ K → (∀ a b, ‖X a b‖ ≤ K) → |c i (Yl X)| ≤ Cst * K := by
    intro i X K hK hX
    have h1 := real_linear_matrix_functional_entry_bound ((c i).comp Yl) X K hX
    have h2 : (∑ a, ∑ b, (|((c i).comp Yl) (single a b 1)| +
        |((c i).comp Yl) (single a b Complex.I)|)) ≤ Cst := by
      have := Finset.single_le_sum (f := fun i => ∑ a, ∑ b, (|((c i).comp Yl) (single a b 1)| +
        |((c i).comp Yl) (single a b Complex.I)|)) (fun i _ => by positivity) (Finset.mem_univ i)
      linarith
    calc |c i (Yl X)| = |((c i).comp Yl) X| := rfl
      _ ≤ _ := h1
      _ ≤ Cst * K := by gcongr
  set τ : ℝ := min (1 / (2 * Cst)) (smax - 1) with hτ
  have hτpos : 0 < τ := lt_min (by positivity) (by linarith)
  have hτle : τ ≤ 1 / (2 * Cst) := min_le_left _ _
  have hτle' : τ ≤ smax - 1 := min_le_right _ _
  set M : Fin k → Matrix (Fin d) (Fin d) ℂ := fun j =>
    if j = i0 then (1/2 : ℝ) • (1 - (1 + τ) • G i0) else G j with hM
  have hci01 : c i0 1 = 1 := by
    rw [← hsum', map_sum]; simp [hGdef, hdual]
  have hMj : ∀ j, j ≠ i0 → M j = G j := fun j hj => by simp [hM, hj]
  have hMi0 : M i0 = (1/2 : ℝ) • (1 - (1 + τ) • G i0) := by simp [hM]
  refine ⟨M, ?_, ?_, ?_⟩
  · intro j
    by_cases hj : j = i0
    · rw [hj, hMi0]
      constructor
      · have e : (1 : Matrix (Fin d) (Fin d) ℂ) - (1 + τ) • G i0
            = (1 - smax • G i0) + (smax - (1 + τ)) • G i0 := by rw [sub_smul]; abel
        rw [e]
        exact (hsPSD.add ((hGpsd i0).smul (by linarith : (0:ℝ) ≤ smax - (1 + τ)))).smul
          (by norm_num : (0:ℝ) ≤ 1/2)
      · have e : (1 : Matrix (Fin d) (Fin d) ℂ) - (1/2 : ℝ) • (1 - (1 + τ) • G i0)
            = (1/2 : ℝ) • (1 : Matrix (Fin d) (Fin d) ℂ) + ((1 + τ) / 2) • G i0 := by
          rw [smul_sub, smul_smul]; ext a b; simp [Matrix.one_apply]; split_ifs <;> ring
        rw [e]
        exact (PosSemidef.one.smul (by norm_num : (0:ℝ) ≤ 1/2)).add
          ((hGpsd i0).smul (by positivity))
    · rw [hMj j hj]
      refine ⟨hGpsd j, ?_⟩
      have e := hsum'
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at e
      rw [← e, add_sub_cancel_left]
      exact posSemidef_sum _ fun i _ => hGpsd i
  · rintro ⟨H, hHpsd, hHsum, hHmarg⟩
    have hle : ∀ σ j, σ j = true → (M j - H σ).PosSemidef := by
      intro σ j hσ
      have e := hHmarg j
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ σ), if_pos hσ] at e
      rw [← e, add_sub_cancel_left]
      exact posSemidef_sum _ fun τ _ => by
        split_ifs
        · exact hHpsd τ
        · exact PosSemidef.zero
    have hcH : ∀ σ j, j ≠ i0 → σ j = true → ∃ a : ℝ, 0 ≤ a ∧ H σ = a • G j := by
      intro σ j hj hσ
      have := hle σ j hσ
      rw [hMj j hj] at this
      exact rank_one_psd_dominated_eq_smul (H σ) (g j) (hHpsd σ) this
    have hvan : ∀ σ j l, j ≠ i0 → l ≠ i0 → j ≠ l → σ j = true → σ l = true → H σ = 0 := by
      intro σ j l hj hl hjl hσj hσl
      obtain ⟨a, -, ha⟩ := hcH σ j hj hσj
      obtain ⟨b, -, hb⟩ := hcH σ l hl hσl
      have h1 : c j (H σ) = a := by rw [ha, map_smul, hdual]; simp
      have h2 : c j (H σ) = 0 := by rw [hb, map_smul, hdual]; simp [hjl]
      rw [ha, ← h1, h2, zero_smul]
    set N := Finset.univ.filter (fun τ : Fin k → Bool => ∀ j, j ≠ i0 → τ j = false) with hN
    have hnotN : ∀ τ, τ ∉ N → ∃ j, j ≠ i0 ∧ τ j = true := by
      intro τ hτN
      simp only [hN, Finset.mem_filter, Finset.mem_univ, true_and] at hτN
      push Not at hτN
      obtain ⟨j, hj, h⟩ := hτN
      exact ⟨j, hj, by simpa using h⟩
    have hpt : ∀ τ, H τ = (if τ ∈ N then H τ else 0) +
        ∑ j ∈ Finset.univ.erase i0, (if τ j then H τ else 0) := by
      intro τ
      by_cases hτN : τ ∈ N
      · rw [if_pos hτN]
        have : ∀ j ∈ Finset.univ.erase i0, (if τ j then H τ else 0) = 0 := by
          intro j hj
          have := (Finset.mem_filter.mp hτN).2 j (Finset.ne_of_mem_erase hj)
          simp [this]
        rw [Finset.sum_eq_zero this, add_zero]
      · rw [if_neg hτN, zero_add]
        obtain ⟨j, hj, hτj⟩ := hnotN τ hτN
        rw [Finset.sum_eq_single_of_mem j (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ _⟩)]
        · simp [hτj]
        · intro l hl hlj
          by_cases hτl : τ l = true
          · simp [hτl, hvan τ j l hj (Finset.ne_of_mem_erase hl) (Ne.symm hlj) hτj hτl]
          · simp [hτl]
    have hNsum : ∑ τ ∈ N, H τ = G i0 := by
      have e1 : (1 : Matrix (Fin d) (Fin d) ℂ) = ∑ τ ∈ N, H τ + ∑ j ∈ Finset.univ.erase i0, G j := by
        rw [← hHsum]
        conv_lhs => rw [Finset.sum_congr rfl fun τ _ => hpt τ]
        rw [Finset.sum_add_distrib, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [hHmarg j, hMj j (Finset.ne_of_mem_erase hj)]
      have e2 := hsum'
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i0)] at e2
      exact (add_right_cancel (e2.trans e1)).symm
    have hc0H : ∀ σ, 0 ≤ c i0 (H σ) := by
      intro σ
      by_cases hσN : σ ∈ N
      · have hle0 : (vecMulVec (g i0) (star (g i0)) - H σ).PosSemidef := by
          change (G i0 - H σ).PosSemidef
          rw [← hNsum, ← Finset.add_sum_erase _ _ hσN, add_sub_cancel_left]
          exact posSemidef_sum _ fun τ _ => hHpsd τ
        obtain ⟨a, ha, he⟩ := rank_one_psd_dominated_eq_smul (H σ) (g i0) (hHpsd σ) hle0
        rw [he, map_smul, hdual]; simp [ha]
      · obtain ⟨j, hj, hσj⟩ := hnotN σ hσN
        obtain ⟨a, -, he⟩ := hcH σ j hj hσj
        rw [he, map_smul, hdual]; simp [Ne.symm hj]
    have hlhs : c i0 (M i0) = -τ / 2 := by
      rw [hMi0, map_smul, map_sub, map_smul, hci01, hdual]; simp; ring
    have hrhs : 0 ≤ c i0 (M i0) := by
      rw [← hHmarg i0, map_sum]
      exact Finset.sum_nonneg fun σ _ => by
        split_ifs
        · exact hc0H σ
        · simp
    linarith
  · rintro P ⟨hPH, hPP, hPr⟩
    set Q : Matrix (Fin d) (Fin d) ℂ := 1 - P with hQ
    have hQH : Q.IsHermitian := isHermitian_one.sub hPH
    have hQQ : Q * Q = Q := by simp [hQ, sub_mul, mul_sub, hPP]
    have hPQ : P * Q = 0 := by simp [hQ, mul_sub, hPP]
    have hQP : Q * P = 0 := by simp [hQ, sub_mul, hPP]
    set K := Q.trace.re with hK
    have hent := hermitian_idempotent_entry_norm_le_trace_re Q hQH hQQ
    have hKpos : 0 < K := by
      by_contra hK0
      push Not at hK0
      have hQ0 : Q = 0 := by
        ext a b
        have h1 := hent a b
        have : ‖Q a b‖ = 0 := le_antisymm (by linarith) (norm_nonneg _)
        simpa using this
      have hP1 : P = 1 := (sub_eq_zero.mp hQ0).symm
      rw [hP1, rank_one] at hPr
      simp at hPr
    set Y := Yl Q with hY
    have hFinvH : (F⁻¹).conjTranspose = F⁻¹ := by rw [conjTranspose_nonsing_inv, hF.eq]
    have hYH : Y.IsHermitian := by
      rw [IsHermitian, hY, hYl_apply, conjTranspose_smul, conjTranspose_add, conjTranspose_mul,
        conjTranspose_mul, hFinvH, hQH.eq, add_comm]
      simp
    have hβ0 : c i0 Y = K := by
      rw [hc0 Y hYH, hY, hYl_apply, Matrix.mul_smul, Matrix.mul_add, ← Matrix.mul_assoc,
        mul_nonsing_inv F hFu, Matrix.one_mul, trace_smul, trace_add, ← Matrix.mul_assoc,
        trace_mul_comm (F * Q) F⁻¹, ← Matrix.mul_assoc, nonsing_inv_mul F hFu, Matrix.one_mul]
      simp [hK]; ring
    have hPQX : ∀ X : Matrix (Fin d) (Fin d) ℂ, P * (Q * X) = 0 := by
      intro X; rw [← Matrix.mul_assoc, hPQ, Matrix.zero_mul]
    have hPYP : P * Y * P = 0 := by
      rw [hY, hYl_apply]
      simp [Matrix.mul_add, Matrix.mul_assoc, hQP, hPQX]
    have hYexp := hspan Y hYH
    have hPYP' : ∑ i, c i Y • (P * G i * P) = 0 := by
      rw [← hPYP]
      conv_rhs => rw [hYexp]
      rw [Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mul_smul, Matrix.smul_mul]
    have hβb : ∀ i, |c i Y| ≤ Cst * K := fun i => hbound i Q K hKpos.le hent
    set t : ℝ := 1 / (2 * Cst * K) with ht
    have htpos : 0 < t := by positivity
    have htK : t * (Cst * K) = 1 / 2 := by rw [ht]; field_simp
    set α : Fin k → ℝ := fun i => 1/2 - (if i = i0 then (1 + τ) / 2 else 0) + t * c i Y with hα
    have hαb : ∀ i, 0 ≤ α i ∧ α i ≤ 1 := by
      intro i
      have htb : |t * c i Y| ≤ 1/2 := by
        rw [abs_mul, abs_of_pos htpos, ← htK]
        exact mul_le_mul_of_nonneg_left (hβb i) htpos.le
      by_cases hi : i = i0
      · have e : α i = -τ / 2 + 1 / (2 * Cst) := by
          rw [hα]; simp only [hi, if_true, hβ0]; rw [ht]; field_simp; ring
        have h2 : 1 / (2 * Cst) ≤ 1/2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; linarith
        rw [e]; constructor <;> linarith
      · have e : α i = 1/2 + t * c i Y := by rw [hα]; simp [hi]
        rw [e]; have := abs_le.mp htb; constructor <;> linarith
    set pat : Fin k → Bool → (Fin k → Bool) := fun i b j => if j = i0 then b else decide (j = i)
      with hpat
    set w : Fin k → Bool → ℝ := fun i b => if b then α i else 1 - α i with hw
    have hw0 : ∀ i b, 0 ≤ w i b := by
      intro i b; cases b <;> simp [hw] <;> linarith [(hαb i).1, (hαb i).2]
    have hwsum : ∀ i, w i true + w i false = 1 := by intro i; simp [hw]
    have hPGP : ∀ i, (P * G i * P).PosSemidef := by
      intro i; have := (hGpsd i).mul_mul_conjTranspose_same P; rwa [hPH.eq] at this
    refine ⟨fun σ => ∑ i, ∑ b, if σ = pat i b then w i b • (P * G i * P) else 0, ?_, ?_, ?_⟩
    · intro σ
      exact posSemidef_sum _ fun i _ => posSemidef_sum _ fun b _ => by
        split_ifs
        · exact (hPGP i).smul (hw0 i b)
        · exact PosSemidef.zero
    · calc ∑ σ, ∑ i, ∑ b, (if σ = pat i b then w i b • (P * G i * P) else 0)
          = ∑ i, ∑ b, ∑ σ, (if σ = pat i b then w i b • (P * G i * P) else 0) := by
            rw [Finset.sum_comm]; exact Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ i, ∑ b, w i b • (P * G i * P) := by simp
        _ = ∑ i, P * G i * P := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Fintype.sum_bool, ← add_smul, hwsum, one_smul]
        _ = P := by rw [← Finset.sum_mul, ← Finset.mul_sum, hsum', Matrix.mul_one, hPP]
    · intro j
      have step : ∀ σ : Fin k → Bool,
          (if σ j then ∑ i, ∑ b, (if σ = pat i b then w i b • (P * G i * P) else 0) else 0)
          = ∑ i, ∑ b, (if σ = pat i b then
              (if pat i b j then w i b • (P * G i * P) else 0) else 0) := by
        intro σ
        by_cases hσ : σ j = true
        · rw [if_pos hσ]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
          by_cases h : σ = pat i b
          · rw [if_pos h, if_pos h, ← h, if_pos hσ]
          · rw [if_neg h, if_neg h]
        · rw [if_neg hσ]
          symm
          refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun b _ => ?_
          by_cases h : σ = pat i b
          · rw [if_pos h, ← h, if_neg hσ]
          · rw [if_neg h]
      rw [Finset.sum_congr rfl fun σ _ => step σ, Finset.sum_comm]
      rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      by_cases hj : j = i0
      · subst hj
        have hpj : ∀ i b, pat i b j = b := by intro i b; simp [hpat]
        simp only [hpj, Fintype.sum_bool, if_true, Bool.false_eq_true, if_false, add_zero]
        have hwt : ∀ x, w x true = α x := by intro x; simp [hw]
        simp only [hwt]
        have hX : ∑ x, P * G x * P = P := by
          rw [← Finset.sum_mul, ← Finset.mul_sum, hsum', Matrix.mul_one, hPP]
        have lhs : ∑ x, α x • (P * G x * P) = (1/2 : ℝ) • P - ((1 + τ) / 2) • (P * G j * P) := by
          simp only [hα, add_smul, sub_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib,
            ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_smul]
          rw [← Finset.smul_sum, hX, ← Finset.smul_sum, hPYP', smul_zero, add_zero]
        have rhs : P * ((1/2 : ℝ) • (1 - (1 + τ) • G j)) * P
            = (1/2 : ℝ) • P - ((1 + τ) / 2) • (P * G j * P) := by
          rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP,
            Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_smul]
          congr 2; ring
        rw [lhs, hMi0, rhs]
      · have hpj : ∀ i b, pat i b j = decide (j = i) := by intro i b; simp [hpat, hj]
        simp only [hpj, decide_eq_true_eq]
        rw [Finset.sum_eq_single j]
        · simp only [if_true, hMj j hj]
          rw [Fintype.sum_bool, ← add_smul, hwsum, one_smul]
        · intro i _ hij; simp [Ne.symm hij]
        · simp
