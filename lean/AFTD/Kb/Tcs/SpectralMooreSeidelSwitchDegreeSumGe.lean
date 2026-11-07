import AFTD.Prelude
import AFTD.Kb.Tcs.SpectralMooreSeidelSwitch

/-!
# spectral_moore_seidel_switch_degree_sum_ge

Topic: graphs   Node: b6422300b360

Provenance: helper lemma. arXiv:2611.00591 (A spectral Moore problem and the Yang-Koolen conjecture), Section 5, Lemma 5.2, inequality (13)

Let G be a k-regular finite simple graph on V with n = |V| ≥ 2k + 2, X : Set V, and suppose every vertex of the Seidel switching F = spectral_moore_seidel_switch G X has degree at most d0, where d0 < k. Then n * ((n - 2k + 1) / 2) ≤ ∑ v, F.degree v + 2 * d0 ^ 2 (natural-number division and subtraction); that is, the average degree of F is at least ⌈(n - 2k)/2⌉ - 2 d0²/n.
-/

open Classical SimpleGraph Matrix in
theorem spectral_moore_seidel_switch_degree_sum_ge {V : Type*} [Fintype V]
    (G : SimpleGraph V) (X : Set V) (k d0 : ℕ) (hreg : G.IsRegularOfDegree k) (hd0 : d0 < k)
    (hF : ∀ v, (spectral_moore_seidel_switch G X).degree v ≤ d0)
    (hn : 2 * k + 2 ≤ Fintype.card V) :
    Fintype.card V * ((Fintype.card V - 2 * k + 1) / 2) ≤
      ∑ v, (spectral_moore_seidel_switch G X).degree v + 2 * d0 ^ 2 := by
  set F := spectral_moore_seidel_switch G X with hFdef
  set n := Fintype.card V with hndef
  set s : V → ℝ := fun v => if v ∈ X then 1 else -1 with hs
  have hs2 : ∀ v, s v * s v = 1 := by intro v; simp only [hs]; split_ifs <;> norm_num
  have hentry : ∀ u v, F.adjMatrix ℝ u v = (1 - s u * s v) / 2 + s u * s v * G.adjMatrix ℝ u v := by
    intro u v
    by_cases huv : u = v
    · subst huv; simp [hs2]
    have hadj : F.Adj u v ↔ (G.Adj u v ↔ (u ∈ X ↔ v ∈ X)) := by
      change u ≠ v ∧ _ ↔ _
      simp [huv]
    rw [adjMatrix_apply, adjMatrix_apply]
    simp only [hs]
    by_cases hu : u ∈ X <;> by_cases hv : v ∈ X <;> by_cases hG : G.Adj u v <;>
      simp [hu, hv, hG, hadj]
  set R : V → ℝ := fun v => ∑ u, G.adjMatrix ℝ v u * s u with hR
  set T : ℝ := ∑ u, s u with hT
  have hrow : ∀ v, ∑ u, G.adjMatrix ℝ v u = k := by
    intro v
    have := G.adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := v)
    simpa [mulVec, dotProduct, hreg.degree_eq] using this
  have hRle : ∀ v, |R v| ≤ k := by
    intro v
    rw [abs_le, ← hrow v]
    constructor
    · rw [← Finset.sum_neg_distrib]
      simp only [hR]
      refine Finset.sum_le_sum fun u _ => ?_
      have h0 : 0 ≤ G.adjMatrix ℝ v u := by rw [adjMatrix_apply]; split_ifs <;> norm_num
      have : -1 ≤ s u := by simp only [hs]; split_ifs <;> norm_num
      nlinarith
    · simp only [hR]
      refine Finset.sum_le_sum fun u _ => ?_
      have h0 : 0 ≤ G.adjMatrix ℝ v u := by rw [adjMatrix_apply]; split_ifs <;> norm_num
      have : s u ≤ 1 := by simp only [hs]; split_ifs <;> norm_num
      nlinarith
  have hdeg : ∀ v, (F.degree v : ℝ) = (n - s v * T) / 2 + s v * R v := by
    intro v
    have := F.adjMatrix_mulVec_const_apply (α := ℝ) (a := 1) (v := v)
    rw [mul_one] at this
    rw [← this]
    simp only [mulVec, dotProduct, Function.const_apply, mul_one, hentry, Finset.sum_add_distrib,
      ← Finset.sum_div, Finset.sum_sub_distrib, hR, hT, Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, hndef]
    congr 1
    exact Finset.sum_congr rfl fun u _ => by ring
  have hsumR : ∑ v, R v = k * T := by
    simp only [hR, hT]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [← Finset.sum_mul, ← hrow u]
    congr 1
    exact Finset.sum_congr rfl fun v _ => by
      rw [(G.isSymm_adjMatrix (α := ℝ)).apply]
  have hterm : ∀ v, s v * R v + k = |R v + k * s v| := by
    intro v
    have := hRle v
    rw [abs_le] at this
    simp only [hs] at this ⊢
    split_ifs
    · rw [abs_of_nonneg (by linarith)]; ring
    · rw [abs_of_nonpos (by linarith)]; ring
  have hkey : 2 * k * |T| ≤ ∑ v, (s v * R v + k) := by
    simp only [hterm]
    refine le_trans ?_ (Finset.abs_sum_le_sum_abs _ _)
    rw [Finset.sum_add_distrib, hsumR, ← Finset.mul_sum, ← hT]
    rw [show (k : ℝ) * T + k * T = 2 * k * T by ring, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * k)]
  have hsumdeg : ∑ v, (F.degree v : ℝ) = (n * n - T * T) / 2 + ∑ v, s v * R v := by
    simp only [hdeg, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
      ← Finset.sum_mul, ← hT, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hndef]
  have hsR : ∑ v, s v * R v ≥ 2 * k * |T| - k * n := by
    have := hkey
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [← hndef] at this
    linarith
  have hlow : ∀ v, (n - s v * T) / 2 - k ≤ d0 := by
    intro v
    have h1 := hdeg v
    have h2 : (F.degree v : ℝ) ≤ d0 := by exact_mod_cast hF v
    have h3 := hRle v
    have h4 : -(k : ℝ) ≤ s v * R v := by
      rw [abs_le] at h3
      simp only [hs]; split_ifs <;> linarith [h3.1, h3.2]
    linarith
  have hcard_pos : 0 < n := by omega
  have hallX : ∀ σ : ℝ, (∀ v, s v = σ) → σ * σ = 1 → False := by
    intro σ hσ hσ2
    obtain ⟨v⟩ : Nonempty V := Fintype.card_pos_iff.mp (by rw [← hndef]; exact hcard_pos)
    have hRv : R v = σ * k := by
      simp only [hR, hσ, ← Finset.sum_mul, hrow]; ring
    have hTv : T = σ * n := by
      simp only [hT, hσ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hndef]; ring
    have h1 := hdeg v
    rw [hσ v, hRv, hTv] at h1
    have h2 : (F.degree v : ℝ) ≤ d0 := by exact_mod_cast hF v
    have h3 : (d0 : ℝ) < k := by exact_mod_cast hd0
    have : (F.degree v : ℝ) = k := by rw [h1]; linear_combination (k - n / 2) * hσ2
    linarith
  have hX : ∃ v, s v = 1 := by
    by_contra h
    push Not at h
    exact hallX (-1) (fun v => by have := h v; simp only [hs] at this ⊢; split_ifs at this ⊢ <;> simp_all) (by norm_num)
  have hY : ∃ v, s v = -1 := by
    by_contra h
    push Not at h
    exact hallX 1 (fun v => by have := h v; simp only [hs] at this ⊢; split_ifs at this ⊢ <;> simp_all) (by norm_num)
  obtain ⟨v1, hv1⟩ := hX
  obtain ⟨v2, hv2⟩ := hY
  have hl1 := hlow v1
  have hl2 := hlow v2
  rw [hv1] at hl1
  rw [hv2] at hl2
  -- parity of T
  set a := (Finset.univ.filter (fun v => v ∈ X)).card with ha
  have hTa : T = 2 * (a : ℝ) - n := by
    simp only [hT, hs, Finset.sum_ite, Finset.sum_const, nsmul_eq_mul, mul_one, mul_neg]
    have := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun v => v ∈ X)
    rw [Finset.card_univ, ← hndef, ← ha] at this
    have h' : ((Finset.univ.filter (fun v => ¬ v ∈ X)).card : ℝ) = n - a := by
      rw [← this]; push_cast; ring
    rw [h']; ring
  have ha_le : a ≤ n := by
    rw [ha, hndef]; exact (Finset.card_filter_le _ _).trans (by rw [Finset.card_univ])
  set c := (n - 2 * k + 1) / 2 with hc
  have hc1 : 2 * c + 2 * k ≤ n + 1 := by omega
  have hc1r : 2 * (c : ℝ) + 2 * k ≤ n + 1 := by exact_mod_cast hc1
  have hd0r : (0 : ℝ) ≤ d0 := by positivity
  have hnr : 2 * (k : ℝ) + 2 ≤ n := by exact_mod_cast hn
  have hkr : (0 : ℝ) ≤ k := by positivity
  have goal : (n : ℝ) * c ≤ ∑ v, (F.degree v : ℝ) + 2 * (d0 : ℝ) ^ 2 := by
    rw [hsumdeg]
    rcases eq_or_ne (2 * a) n with h2a | h2a
    · have hT0 : T = 0 := by rw [hTa]; exact_mod_cast (by omega : (2 * a : ℤ) - n = 0)
      have hc0 : 2 * c + 2 * k ≤ n := by omega
      have hc0r : 2 * (c : ℝ) + 2 * k ≤ n := by exact_mod_cast hc0
      rw [hT0, abs_zero] at hsR
      rw [hT0]
      nlinarith
    · have hT1 : 1 ≤ |T| := by
        rw [hTa]
        have : (1 : ℤ) ≤ |(2 * a : ℤ) - n| := Int.one_le_abs (by omega)
        exact_mod_cast this
      have hTT : T * T = |T| * |T| := (abs_mul_abs_self T).symm
      have hm : (n : ℝ) - 2 * k + |T| ≤ 2 * d0 := by
        rcases abs_cases T with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;> linarith
      rw [hTT]
      have hn0 : (0 : ℝ) ≤ n := by positivity
      have F1 : (n : ℝ) * (2 * c + 2 * k) ≤ n * (n + 1) := mul_le_mul_of_nonneg_left hc1r hn0
      have F2 : ((n : ℝ) - 2 * k + |T|) * ((n : ℝ) - 2 * k + |T|) ≤ (2 * d0) * (2 * d0) :=
        mul_self_le_mul_self (by linarith) hm
      have F3 : 0 ≤ ((n : ℝ) - 2 * k) * ((n : ℝ) - 2 * k + 2 * |T| - 1) :=
        mul_nonneg (by linarith) (by linarith)
      have F4 : 0 ≤ (k : ℝ) * (|T| - 1) := mul_nonneg hkr (by linarith)
      linarith
  exact_mod_cast goal
