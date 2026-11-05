import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralNormC

/-!
# fourier_entropy_block_bound

Topic: circuits   Node: e93a906fda0d

Provenance: helper lemma. arXiv:2611.06451 Theorem 3.1 proof (eq. 18)

Let f, P : (Fin n → Bool) → ℂ and let T be a set of frequencies with non-zero Fourier coefficients |f_hat(S)| > 0 such that |f_hat(S)| ≤ 2 * |P_hat(S)| for all S in T. If mu = ∑_{S ∈ T} |f_hat(S)|^2 > 0, then ∑_{S ∈ T} |f_hat(S)|^2 * log_2(1 / |f_hat(S)|^2) ≤ 2 * mu * (1 + log_2(max 1 ||P_hat||_1) + log_2(1 / mu)).
-/

theorem fourier_entropy_block_bound_logsum {ι : Type*} (T : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ T, 0 < u i) (hsum : ∑ i ∈ T, u i ^ 2 = 1) :
    ∑ i ∈ T, u i ^ 2 * Real.log (1 / u i) ≤ Real.log (∑ i ∈ T, u i) := by
  have hne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hsum; simp at hsum
  have hU : 0 < ∑ i ∈ T, u i := Finset.sum_pos (fun i hi => hu i hi) hne
  have hterm : ∀ i ∈ T, u i ^ 2 - u i / (∑ j ∈ T, u j) ≤ u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j) := by
    intro i hi
    have hui : 0 < u i := hu i hi
    have hpos : (0:ℝ) < (u i * ∑ j ∈ T, u j)⁻¹ := by positivity
    have h0 : Real.log ((u i * ∑ j ∈ T, u j)⁻¹) ≤ (u i * ∑ j ∈ T, u j)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos hpos
    rw [Real.log_inv] at h0
    have hlog : 1 - 1 / (u i * ∑ j ∈ T, u j) ≤ Real.log (u i * ∑ j ∈ T, u j) := by
      have h2 : (1:ℝ) / (u i * ∑ j ∈ T, u j) = (u i * ∑ j ∈ T, u j)⁻¹ := one_div _
      linarith [h0, h2]
    have hmul : u i ^ 2 * (1 - 1 / (u i * ∑ j ∈ T, u j)) ≤ u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j) :=
      mul_le_mul_of_nonneg_left hlog (sq_nonneg _)
    have heq : u i ^ 2 * (1 - 1 / (u i * ∑ j ∈ T, u j)) = u i ^ 2 - u i / (∑ j ∈ T, u j) := by
      have h1 := hui; have h2 := hU; field_simp
    linarith [hmul, heq]
  have hge : 0 ≤ ∑ i ∈ T, u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j) := by
    have h1 : ∑ i ∈ T, (u i ^ 2 - u i / (∑ j ∈ T, u j)) ≤ ∑ i ∈ T, u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j) :=
      Finset.sum_le_sum hterm
    have h2 : ∑ i ∈ T, (u i ^ 2 - u i / (∑ j ∈ T, u j)) = 0 := by
      rw [Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      rw [hsum, div_self (ne_of_gt hU)]
      ring
    linarith [h1, h2]
  have hsplit : ∑ i ∈ T, u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j)
      = ∑ i ∈ T, u i ^ 2 * Real.log (u i) + Real.log (∑ j ∈ T, u j) := by
    have hcongr : ∀ i ∈ T, u i ^ 2 * Real.log (u i * ∑ j ∈ T, u j)
        = u i ^ 2 * Real.log (u i) + u i ^ 2 * Real.log (∑ j ∈ T, u j) := by
      intro i hi
      rw [Real.log_mul (ne_of_gt (hu i hi)) (ne_of_gt hU)]
      ring
    rw [Finset.sum_congr rfl hcongr, Finset.sum_add_distrib, ← Finset.sum_mul, hsum]
    ring
  have hgoal : ∑ i ∈ T, u i ^ 2 * Real.log (u i) ≥ - Real.log (∑ j ∈ T, u j) := by
    linarith [hge, hsplit]
  have hconv : ∑ i ∈ T, u i ^ 2 * Real.log (1 / u i) = - ∑ i ∈ T, u i ^ 2 * Real.log (u i) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [one_div, Real.log_inv]
    ring
  rw [hconv]
  linarith [hgoal]

theorem fourier_entropy_block_bound_logsum_logb {ι : Type*} (T : Finset ι) (u : ι → ℝ)
    (hu : ∀ i ∈ T, 0 < u i) (hsum : ∑ i ∈ T, u i ^ 2 = 1) :
    ∑ i ∈ T, u i ^ 2 * Real.logb 2 (1 / u i) ≤ Real.logb 2 (∑ i ∈ T, u i) := by
  have h := fourier_entropy_block_bound_logsum T u hu hsum
  have hD : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hterm : ∀ i ∈ T, u i ^ 2 * Real.logb 2 (1/u i) = (u i^2 * Real.log (1/u i)) / Real.log 2 := by
    intro i hi; rw [Real.logb, mul_div_assoc]
  have hsum_eq : ∑ i ∈ T, u i ^ 2 * Real.logb 2 (1 / u i)
      = (∑ i ∈ T, u i ^ 2 * Real.log (1 / u i)) / Real.log 2 := by
    rw [Finset.sum_congr rfl hterm]
    exact (Finset.sum_div T (fun i => u i ^ 2 * Real.log (1 / u i)) (Real.log 2)).symm
  rw [hsum_eq, Real.logb]
  exact (div_le_div_iff_of_pos_right hD).mpr h

theorem fourier_entropy_block_bound_aux {ι : Type*} (T : Finset ι) (a b : ι → ℝ) (A mu : ℝ)
    (ha : ∀ S ∈ T, 0 ≤ a S) (hb : ∀ S ∈ T, 0 ≤ b S)
    (hT : ∀ S ∈ T, a S ≤ 2 * b S)
    (ha0 : ∀ S ∈ T, a S ≠ 0)
    (hmu : mu = ∑ S ∈ T, a S ^ 2) (hmu_pos : 0 < mu)
    (hA1 : 1 ≤ A) (hAb : ∑ S ∈ T, b S ≤ A) :
    ∑ S ∈ T, a S ^ 2 * Real.logb 2 (1 / a S ^ 2)
      ≤ 2 * mu * (1 + Real.logb 2 A + Real.logb 2 (1 / mu)) := by
  have ha_pos : ∀ S ∈ T, 0 < a S := fun S hS => lt_of_le_of_ne (ha S hS) (Ne.symm (ha0 S hS))
  have hne : T.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro h; rw [h] at hmu; simp at hmu; linarith [hmu_pos, hmu]
  have hUpos : 0 < ∑ S ∈ T, a S := Finset.sum_pos (fun S hS => ha_pos S hS) hne
  have hUle : ∑ S ∈ T, a S ≤ 2 * A := by
    have h1 : ∑ S ∈ T, a S ≤ ∑ S ∈ T, 2 * b S := Finset.sum_le_sum hT
    have h2 : ∑ S ∈ T, 2 * b S = 2 * ∑ S ∈ T, b S := by rw [Finset.mul_sum]
    have h3 : 2 * ∑ S ∈ T, b S ≤ 2 * A := by linarith [mul_le_mul_of_nonneg_left hAb (by norm_num : (0:ℝ) ≤ 2)]
    linarith
  have hsqrtpos : 0 < Real.sqrt mu := Real.sqrt_pos.mpr hmu_pos
  have hsq_sqrt : Real.sqrt mu ^ 2 = mu := Real.sq_sqrt (le_of_lt hmu_pos)
  set u : ι → ℝ := fun S => a S / Real.sqrt mu with hu_def
  have hu : ∀ S ∈ T, 0 < u S := by
    intro S hS; rw [hu_def]; exact div_pos (ha_pos S hS) hsqrtpos
  have hsumu : ∑ S ∈ T, u S ^ 2 = 1 := by
    have hterm : ∀ S ∈ T, u S ^ 2 = a S ^ 2 / mu := by
      intro S hS; rw [hu_def]; rw [div_pow, hsq_sqrt]
    rw [Finset.sum_congr rfl hterm, ← Finset.sum_div, ← hmu, div_self (ne_of_gt hmu_pos)]
  have hentropy : ∑ S ∈ T, u S ^ 2 * Real.logb 2 (1 / u S) ≤ Real.logb 2 (∑ S ∈ T, u S) :=
    fourier_entropy_block_bound_logsum_logb T u hu hsumu
  have hsumu_val : ∑ S ∈ T, u S = (∑ S ∈ T, a S) / Real.sqrt mu := by
    rw [hu_def]; exact (Finset.sum_div T a (Real.sqrt mu)).symm
  have hsumu_pos : 0 < ∑ S ∈ T, u S := by rw [hsumu_val]; positivity
  have hlogsqrt : Real.logb 2 (Real.sqrt mu) = (1 / 2) * Real.logb 2 mu := by
    have h := Real.logb_pow 2 (Real.sqrt mu) 2
    rw [hsq_sqrt] at h
    push_cast at h
    linarith
  have hone : Real.logb 2 (2:ℝ) = 1 := by
    rw [Real.logb]; rw [div_self (ne_of_gt (Real.log_pos (by norm_num)))]
  have hval : Real.logb 2 (2*A/Real.sqrt mu) = 1 + Real.logb 2 A + (1/2)*Real.logb 2 (1/mu) := by
    have hAne : A ≠ 0 := by linarith [hA1]
    have hdiv := Real.logb_div (b:=2) (x:=2*A) (y:=Real.sqrt mu) (by positivity) (ne_of_gt hsqrtpos)
    have hmul := Real.logb_mul (b:=2) (x:=(2:ℝ)) (y:=A) (by norm_num) hAne
    have h1mu : Real.logb 2 (1/mu) = - Real.logb 2 mu := by rw [one_div, Real.logb_inv]
    rw [hdiv, hmul, hone, h1mu]
    linarith [hlogsqrt]
  have hbound_log : Real.logb 2 (∑ S ∈ T, u S) ≤ 1 + Real.logb 2 A + (1/2)*Real.logb 2 (1/mu) := by
    have hle : ∑ S ∈ T, u S ≤ 2*A/Real.sqrt mu := by
      rw [hsumu_val]; exact (div_le_div_iff_of_pos_right hsqrtpos).mpr hUle
    have hpos2A : 0 < 2*A/Real.sqrt mu := by positivity
    have h := (Real.logb_le_logb (by norm_num : (1:ℝ) < 2) hsumu_pos hpos2A).mpr hle
    rwa [hval] at h
  have hLHS_eq : ∑ S ∈ T, a S ^ 2 * Real.logb 2 (1 / a S ^ 2)
      = mu * (2 * (∑ S ∈ T, u S ^ 2 * Real.logb 2 (1 / u S)) + Real.logb 2 (1 / mu)) := by
    have hterm : ∀ S ∈ T, a S ^ 2 * Real.logb 2 (1 / a S ^ 2)
        = mu * (2 * (u S ^ 2 * Real.logb 2 (1 / u S)) + u S ^ 2 * Real.logb 2 (1 / mu)) := by
      intro S hS
      have huS : u S = a S / Real.sqrt mu := by rw [hu_def]
      have hune : u S ≠ 0 := ne_of_gt (hu S hS)
      have hsq : a S ^ 2 = mu * u S ^ 2 := by rw [huS]; field_simp; rw [hsq_sqrt]
      have hlog : Real.logb 2 (1 / a S ^ 2) = Real.logb 2 (1 / mu) + 2 * Real.logb 2 (1 / u S) := by
        rw [hsq]
        have hm : (1:ℝ) / (mu * u S ^ 2) = (1/mu) * (1/u S ^ 2) := by field_simp
        rw [hm, Real.logb_mul (by positivity) (by positivity)]
        rw [show (1:ℝ)/u S^2 = (1/u S)^2 by ring, Real.logb_pow]
        ring
      rw [hlog, hsq]; ring
    rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]
    congr 1
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, hsumu]
    ring
  rw [hLHS_eq]
  have hinner : 2 * (∑ S ∈ T, u S ^ 2 * Real.logb 2 (1 / u S)) + Real.logb 2 (1 / mu)
      ≤ 2 * (1 + Real.logb 2 A + Real.logb 2 (1 / mu)) := by
    linarith [hentropy, hbound_log]
  calc mu * (2 * (∑ S ∈ T, u S ^ 2 * Real.logb 2 (1 / u S)) + Real.logb 2 (1 / mu))
      ≤ mu * (2 * (1 + Real.logb 2 A + Real.logb 2 (1 / mu))) := mul_le_mul_of_nonneg_left hinner (le_of_lt hmu_pos)
    _ = 2 * mu * (1 + Real.logb 2 A + Real.logb 2 (1 / mu)) := by ring

/-- Entropy contribution of a block of frequencies bounded via concavity of log. -/
theorem fourier_entropy_block_bound {n : ℕ} (f : (Fin n → Bool) → ℂ)
    (T : Finset (Finset (Fin n)))
    (P : (Fin n → Bool) → ℂ)
    (hT : ∀ S ∈ T,
      ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖
      ≤ 2 * ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖)
    (h_pos : ∀ S ∈ T, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ≠ 0)
    (mu : ℝ)
    (hmu : mu = ∑ S ∈ T, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2)
    (hmu_pos : 0 < mu) :
    ∑ S ∈ T, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2 *
      Real.logb 2 (1 / ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ ^ 2)
    ≤ 2 * mu * (1 + Real.logb 2 (max 1 (spectral_norm_c P)) + Real.logb 2 (1 / mu)) := by
  have hAb : (∑ S ∈ T, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖)
      ≤ max 1 (spectral_norm_c P) := by
    have h1 : (∑ S ∈ T, ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖)
        ≤ ∑ S : Finset (Fin n), ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖ :=
      Finset.sum_le_univ_sum_of_nonneg (fun S => norm_nonneg _)
    have h2 : (∑ S : Finset (Fin n), ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖) = spectral_norm_c P := rfl
    have h3 : spectral_norm_c P ≤ max 1 (spectral_norm_c P) := le_max_right _ _
    linarith
  exact fourier_entropy_block_bound_aux T
    (fun S => ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, f x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖)
    (fun S => ‖(1 / (2 : ℂ) ^ n) * ∑ x : Fin n → Bool, P x * (∏ i ∈ S, if x i then (-1 : ℂ) else 1)‖)
    (max 1 (spectral_norm_c P)) mu
    (fun S _ => norm_nonneg _) (fun S _ => norm_nonneg _) hT h_pos hmu hmu_pos (le_max_left _ _) hAb
