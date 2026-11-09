import AFTD.Prelude
import AFTD.Kb.Tcs.RentOrBuyCost
import AFTD.Kb.Tcs.ThresholdSchedule
import AFTD.Kb.Tcs.RentOrBuyNumRuns
import AFTD.Kb.Tcs.ThresholdState
import AFTD.Kb.Tcs.ScheduleHistory
import AFTD.Kb.Tcs.G

/-!
# threshold_schedule_additive_bound

Topic: online_algorithms   Node: 41adac1971fd

Provenance: formalization of a published result. Source: arXiv:2611.06955, Theorem 1(1), additive half; stated for every schedule r, which is the paper's proof and is equivalent to the optimal-schedule form.

For every horizon T ≥ 2, nonnegative increments a : Fin (T - 1) → NNReal with P runs (P = rent_or_buy_num_runs T a), every positive reset price K and every schedule r : Fin T → Bool, the total cost of the threshold schedule is at most the total cost of r plus (2P - 1)K.
-/

noncomputable def ts_g (α : ℝ) (n : ℕ) : ℝ := α * n * (n + 1) / 2

theorem ts_g_zero (α : ℝ) : ts_g α 0 = 0 := by simp [ts_g]
theorem ts_g_succ (α : ℝ) (n : ℕ) : ts_g α (n + 1) = ts_g α n + α * (n + 1) := by
  simp only [ts_g]; push_cast; ring
theorem ts_g_nonneg {α : ℝ} (hα : 0 ≤ α) (n : ℕ) : 0 ≤ ts_g α n := by
  unfold ts_g; positivity
theorem ts_g_zero_rate (n : ℕ) : ts_g 0 n = 0 := by simp [ts_g]

noncomputable def ts_L (α K : ℝ) : ℕ := sInf {n : ℕ | 1 ≤ n ∧ K ≤ ts_g α n}

theorem ts_L_spec {α K : ℝ} (hα : 0 < α) (hK : 0 < K) :
    1 ≤ ts_L α K ∧ K ≤ ts_g α (ts_L α K) ∧ ∀ n, 1 ≤ n → n < ts_L α K → ts_g α n < K := by
  have hne : ({n : ℕ | 1 ≤ n ∧ K ≤ ts_g α n}).Nonempty := by
    obtain ⟨n, hn⟩ := exists_nat_gt (K / α)
    have hn0 : (0 : ℝ) < n := lt_trans (div_pos hK hα) hn
    have h1 : 1 ≤ n := by
      have : 0 < n := by exact_mod_cast hn0
      omega
    refine ⟨n, h1, ?_⟩
    have h2 : K < α * n := by
      have := (div_lt_iff₀ hα).1 hn
      linarith
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast h1
    unfold ts_g
    nlinarith [mul_pos hα hn0]
  have hmem := Nat.sInf_mem hne
  refine ⟨hmem.1, hmem.2, fun n h1 hlt => ?_⟩
  by_contra hcon
  exact Nat.notMem_of_lt_sInf hlt ⟨h1, not_lt.1 hcon⟩

noncomputable def ts_f (α K : ℝ) : ℝ :=
  if 0 < α then (K + ts_g α (ts_L α K)) / (ts_L α K) else 0

theorem ts_f_zero (K : ℝ) : ts_f 0 K = 0 := by simp [ts_f]

theorem ts_f_le {α K : ℝ} (hα : 0 < α) (hK : 0 < K) (n : ℕ) (hn : 1 ≤ n) :
    ts_f α K ≤ (K + ts_g α n) / n := by
  obtain ⟨hL1, hL2, hL3⟩ := ts_L_spec hα hK
  set L := ts_L α K with hLdef
  have hf : ts_f α K = (K + ts_g α L) / L := by simp [ts_f, hα, hLdef]
  rw [hf]
  have up : ∀ m : ℕ, 1 ≤ m → K ≤ ts_g α m →
      (K + ts_g α m) / m ≤ (K + ts_g α (m + 1)) / ((m + 1 : ℕ) : ℝ) := by
    intro m hm hgm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hm0 hm1, ts_g_succ]
    push_cast
    have e : ts_g α m = α * m * (m + 1) / 2 := rfl
    nlinarith [mul_pos hm0 hm0]
  have down : ∀ m : ℕ, 1 ≤ m → ts_g α m ≤ K →
      (K + ts_g α (m + 1)) / ((m + 1 : ℕ) : ℝ) ≤ (K + ts_g α m) / m := by
    intro m hm hgm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
    have hm1 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ hm1 hm0, ts_g_succ]
    push_cast
    have e : ts_g α m = α * m * (m + 1) / 2 := rfl
    nlinarith [mul_pos hm0 hm0]
  rcases le_total L n with hle | hle
  · induction n, hle using Nat.le_induction with
    | base => exact le_rfl
    | succ m hm ih =>
      have hgm : K ≤ ts_g α m := by
        rcases eq_or_lt_of_le hm with h | h
        · rw [← h]; exact hL2
        · by_contra hcon
          -- from monotonicity of `g` on the naturals
          have hmono : ts_g α L ≤ ts_g α m := by
            have hLm : (L : ℝ) ≤ m := by exact_mod_cast hm
            unfold ts_g
            have : (L : ℝ) * (L + 1) ≤ m * (m + 1) := by
              have h0 : (0 : ℝ) ≤ L := by positivity
              nlinarith
            nlinarith
          linarith
      exact (ih (by omega)).trans (up m (by omega) hgm)
  · have key : ∀ d : ℕ, ∀ n : ℕ, n + d = L → 1 ≤ n →
        (K + ts_g α L) / L ≤ (K + ts_g α n) / n := by
      intro d
      induction d with
      | zero => intro n h _; subst h; simp
      | succ d ih =>
        intro n h hn1
        have h1 := ih (n + 1) (by omega) (by omega)
        have hg : ts_g α n ≤ K := (hL3 n hn1 (by omega)).le
        exact h1.trans (down n hn1 hg)
    exact key (L - n) n (by omega) hn

theorem ts_L_mul_le {α K : ℝ} (hα : 0 < α) (hK : 0 < K) :
    α * (ts_L α K) ≤ ts_f α K := by
  obtain ⟨hL1, hL2, hL3⟩ := ts_L_spec hα hK
  set L := ts_L α K with hLdef
  have hf : ts_f α K = (K + ts_g α L) / L := by simp [ts_f, hα, hLdef]
  obtain ⟨m, hm⟩ : ∃ m, L = m + 1 := ⟨L - 1, by omega⟩
  have hgm : ts_g α m ≤ K := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      rw [ts_g_zero]
      exact hK.le
    · exact (hL3 m h (by omega)).le
  rw [hf, hm, le_div_iff₀ (by positivity), ts_g_succ]
  have e : ts_g α m = α * m * (m + 1) / 2 := rfl
  push_cast
  nlinarith

noncomputable def ts_V (α K : ℝ) (j : ℕ) (e : ℝ) : ℝ :=
  K + ts_g α j + j * e - j * ts_f α K

theorem ts_V_nonneg {α K e : ℝ} (hα : 0 < α) (hK : 0 < K) (he : 0 ≤ e) (j : ℕ) :
    0 ≤ ts_V α K j e := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h
    simp [ts_V, ts_g_zero, hK.le]
  · have h1 := ts_f_le hα hK j h
    have hj : (0 : ℝ) < j := by exact_mod_cast h
    rw [le_div_iff₀ hj] at h1
    unfold ts_V
    nlinarith [mul_nonneg hj.le he]

theorem ts_V_L_zero {α K : ℝ} (hα : 0 < α) (hK : 0 < K) : ts_V α K (ts_L α K) 0 = 0 := by
  obtain ⟨hL1, -, -⟩ := ts_L_spec hα hK
  have hL0 : ((ts_L α K : ℕ) : ℝ) ≠ 0 := by
    have : 0 < ts_L α K := hL1
    exact_mod_cast this.ne'
  simp only [ts_V, ts_f, hα, if_true]
  field_simp
  ring

noncomputable def ts_W (α K e : ℝ) : ℝ :=
  if 0 < α then ⨅ j : ℕ, ts_V α K j e else if e = 0 then 0 else K

theorem ts_W_le_V {α K e : ℝ} (hα : 0 < α) (hK : 0 < K) (he : 0 ≤ e) (j : ℕ) :
    ts_W α K e ≤ ts_V α K j e := by
  simp only [ts_W, hα, if_true]
  exact ciInf_le ⟨0, by rintro _ ⟨i, rfl⟩; exact ts_V_nonneg hα hK he i⟩ j

theorem ts_le_W {α K e x : ℝ} (hα : 0 < α) (h : ∀ j, x ≤ ts_V α K j e) : x ≤ ts_W α K e := by
  simp only [ts_W, hα, if_true]
  exact le_ciInf h

theorem ts_W_nonneg {α K e : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) : 0 ≤ ts_W α K e := by
  rcases hα.lt_or_eq with h | h
  · exact ts_le_W h (fun j => ts_V_nonneg h hK he j)
  · subst h
    simp only [ts_W, lt_irrefl, if_false]
    split_ifs <;> linarith

theorem ts_W_le_K {α K e : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) : ts_W α K e ≤ K := by
  rcases hα.lt_or_eq with h | h
  · have := ts_W_le_V h hK he 0
    simpa [ts_V, ts_g_zero] using this
  · subst h
    simp only [ts_W, lt_irrefl, if_false]
    split_ifs <;> linarith

theorem ts_W_zero {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) : ts_W α K 0 = 0 := by
  rcases hα.lt_or_eq with h | h
  · refine le_antisymm ?_ (ts_W_nonneg h.le hK le_rfl)
    have := ts_W_le_V h hK le_rfl (ts_L α K)
    rwa [ts_V_L_zero h hK] at this
  · subst h
    simp [ts_W]

theorem ts_W_mono {α K e e' : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) (hee : e ≤ e') :
    ts_W α K e ≤ ts_W α K e' := by
  rcases hα.lt_or_eq with h | h
  · refine ts_le_W h (fun j => (ts_W_le_V h hK he j).trans ?_)
    simp only [ts_V]
    have : (j : ℝ) * e ≤ j * e' := mul_le_mul_of_nonneg_left hee (by positivity)
    linarith
  · subst h
    simp only [ts_W, lt_irrefl, if_false]
    by_cases h0 : e = 0
    · simp only [h0, if_true]
      split_ifs <;> linarith
    · have : e' ≠ 0 := by
        intro h'
        rw [h'] at hee
        exact h0 (le_antisymm hee he)
      simp [h0, this]

noncomputable def ts_k (α K e acc : ℝ) : ℕ :=
  sInf {k : ℕ | 1 ≤ k ∧ K ≤ acc + ts_g α k + k * e}

theorem ts_k_exists {α K e acc : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) (hacc : 0 ≤ acc)
    (hnot : ¬ (α = 0 ∧ e = 0)) : ∃ k : ℕ, 1 ≤ k ∧ K ≤ acc + ts_g α k + k * e := by
  rcases hα.lt_or_eq with h | h
  · obtain ⟨h1, h2, -⟩ := ts_L_spec h hK
    refine ⟨ts_L α K, h1, ?_⟩
    have : (0 : ℝ) ≤ (ts_L α K : ℝ) * e := by positivity
    linarith
  · subst h
    have he' : 0 < e := lt_of_le_of_ne he (fun h' => hnot ⟨rfl, h'.symm⟩)
    obtain ⟨n, hn⟩ := exists_nat_gt (K / e)
    have hn0 : (0 : ℝ) < n := lt_trans (div_pos hK he') hn
    have h1 : 1 ≤ n := by
      have : 0 < n := by exact_mod_cast hn0
      omega
    refine ⟨n, h1, ?_⟩
    have := (div_lt_iff₀ he').1 hn
    rw [ts_g_zero_rate]
    linarith

theorem ts_k_spec {α K e acc : ℝ} (hne : ∃ k : ℕ, 1 ≤ k ∧ K ≤ acc + ts_g α k + k * e) :
    1 ≤ ts_k α K e acc ∧ K ≤ acc + ts_g α (ts_k α K e acc) + (ts_k α K e acc) * e ∧
      ∀ n, 1 ≤ n → n < ts_k α K e acc → acc + ts_g α n + n * e < K := by
  have hm : ts_k α K e acc ∈ {k : ℕ | 1 ≤ k ∧ K ≤ acc + ts_g α k + k * e} :=
    Nat.sInf_mem hne
  refine ⟨hm.1, hm.2, fun n h1 hlt => ?_⟩
  by_contra hcon
  exact Nat.notMem_of_lt_sInf hlt ⟨h1, not_lt.1 hcon⟩

theorem ts_k_eq {α K e acc : ℝ} {m : ℕ} (h1 : 1 ≤ m) (h2 : K ≤ acc + ts_g α m + m * e)
    (h3 : ∀ n, 1 ≤ n → n < m → acc + ts_g α n + n * e < K) : ts_k α K e acc = m := by
  have hne : ∃ k : ℕ, 1 ≤ k ∧ K ≤ acc + ts_g α k + k * e := ⟨m, h1, h2⟩
  obtain ⟨a1, a2, a3⟩ := ts_k_spec hne
  apply le_antisymm
  · exact Nat.sInf_le ⟨h1, h2⟩
  · by_contra hcon
    exact absurd (h3 _ a1 (not_le.1 hcon)) (not_lt.2 a2)

noncomputable def ts_D (α K e acc : ℝ) : ℝ :=
  if α = 0 ∧ e = 0 then 0 else ts_V α K (ts_k α K e acc) e

theorem ts_D_zero {α K : ℝ} (hα : 0 ≤ α) (hK : 0 < K) : ts_D α K 0 0 = 0 := by
  rcases hα.lt_or_eq with h | h
  · obtain ⟨h1, h2, h3⟩ := ts_L_spec h hK
    have hk : ts_k α K 0 0 = ts_L α K := ts_k_eq h1 (by simpa using h2)
      (fun n a b => by simpa using h3 n a b)
    have hn : ¬ (α = 0 ∧ (0 : ℝ) = 0) := fun ⟨h', _⟩ => h.ne' h'
    unfold ts_D
    rw [if_neg hn, hk]
    exact ts_V_L_zero h hK
  · subst h
    simp [ts_D]

theorem ts_V_succ (α K : ℝ) (j : ℕ) (e : ℝ) :
    ts_V α K (j + 1) e = ts_V α K j (e + α) + e + α - ts_f α K := by
  simp only [ts_V, ts_g_succ]
  push_cast
  ring

theorem ts_W_D {α K e acc : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) (hle : e ≤ acc)
    (hlt : acc < K) (hzero : e = 0 → acc = 0) :
    ts_W α K e ≤ ts_D α K e acc ∧ ts_D α K e acc ≤ ts_W α K e + K := by
  have hacc : 0 ≤ acc := he.trans hle
  rcases hα.lt_or_eq with h | h
  · have hn : ¬ (α = 0 ∧ e = 0) := fun ⟨h', _⟩ => h.ne' h'
    simp only [ts_D, hn, if_false]
    set k := ts_k α K e acc with hkdef
    obtain ⟨hk1, hk2, hk3⟩ := ts_k_spec (ts_k_exists hα hK he hacc hn)
    rw [← hkdef] at hk1 hk2 hk3
    refine ⟨ts_W_le_V h hK he k, ?_⟩
    obtain ⟨hL1, hL2, hL3⟩ := ts_L_spec h hK
    have hkL : k ≤ ts_L α K := Nat.sInf_le ⟨hL1, by
      have : (0 : ℝ) ≤ (ts_L α K : ℝ) * e := by positivity
      linarith⟩
    have hαL := ts_L_mul_le h hK
    have hαk : α * k ≤ ts_f α K := by
      have : (k : ℝ) ≤ ts_L α K := by exact_mod_cast hkL
      nlinarith
    have hf0 : 0 ≤ ts_f α K := le_trans (by positivity) hαk
    have hbound : ∀ j, ts_V α K k e - K ≤ ts_V α K j e := by
      intro j
      by_cases hjk : j < k
      · obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        have hjm : j ≤ m := by omega
        have hmb : acc + ts_g α m + m * e < K := by
          rcases Nat.eq_zero_or_pos m with h0 | h0
          · subst h0
            simpa [ts_g_zero] using hlt
          · exact hk3 m h0 (by omega)
        have hdiff : ((m : ℝ) + 1 - j) * ts_f α K ≥ ts_f α K := by
          have : (1 : ℝ) ≤ (m : ℝ) + 1 - j := by
            have : (j : ℝ) ≤ m := by exact_mod_cast hjm
            linarith
          exact le_mul_of_one_le_left hf0 this
        have hgj := ts_g_nonneg hα j
        have hje : (0 : ℝ) ≤ (j : ℝ) * e := by positivity
        rw [hm]
        simp only [ts_V, ts_g_succ]
        push_cast
        have hα2 : α * ((m : ℝ) + 1) ≤ ts_f α K := by
          have : ((k : ℕ) : ℝ) = (m : ℝ) + 1 := by rw [hm]; push_cast; ring
          rw [this] at hαk
          linarith
        nlinarith
      · have hjk' : k ≤ j := not_lt.1 hjk
        have hVj0 := ts_V_nonneg h hK he j
        by_cases hVk : ts_V α K k e ≤ K
        · linarith
        · have hVk' : K < ts_V α K k e := not_le.1 hVk
          obtain ⟨d, rfl⟩ : ∃ d, j = k + d := ⟨j - k, by omega⟩
          have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
          have hg : ts_g α k = α * k * (k + 1) / 2 := rfl
          have key : 0 < α * (k + 1) / 2 + e - ts_f α K := by
            have h1 : 0 < (k : ℝ) * (α * (k + 1) / 2 + e - ts_f α K) := by
              have : ts_V α K k e - K = (k : ℝ) * (α * (k + 1) / 2 + e - ts_f α K) := by
                simp only [ts_V, hg]; ring
              linarith
            by_contra hc
            have := mul_nonpos_of_nonneg_of_nonpos hk0.le (not_lt.1 hc)
            linarith
          have hdiff : ts_V α K (k + d) e - ts_V α K k e
              = (d : ℝ) * (e - ts_f α K + α * (2 * k + d + 1) / 2) := by
            simp only [ts_V, ts_g]
            push_cast
            ring
          have hmono : 0 ≤ e - ts_f α K + α * (2 * k + d + 1) / 2 := by
            have hd0 : (0 : ℝ) ≤ d := by positivity
            nlinarith
          have : 0 ≤ ts_V α K (k + d) e - ts_V α K k e := by
            rw [hdiff]; exact mul_nonneg (by positivity) hmono
          linarith
    have := ts_le_W h hbound
    linarith
  · subst h
    by_cases h0 : e = 0
    · have hac : acc = 0 := hzero h0
      subst h0; subst hac
      simp [ts_W, ts_D, hK.le]
    · have he' : 0 < e := lt_of_le_of_ne he (Ne.symm h0)
      have hn : ¬ ((0 : ℝ) = 0 ∧ e = 0) := fun ⟨_, h'⟩ => h0 h'
      have hW0 : ts_W 0 K e = K := by simp [ts_W, h0]
      have hD0 : ts_D 0 K e acc = ts_V 0 K (ts_k 0 K e acc) e := if_neg hn
      rw [hW0, hD0]
      set k := ts_k 0 K e acc with hkdef
      obtain ⟨hk1, hk2, hk3⟩ := ts_k_spec (ts_k_exists (α := 0) le_rfl hK he hacc hn)
      rw [← hkdef] at hk1 hk2 hk3
      have hV : ts_V 0 K k e = K + k * e := by
        simp [ts_V, ts_g_zero_rate, ts_f_zero]
      rw [hV]
      constructor
      · have : (0 : ℝ) ≤ (k : ℝ) * e := by positivity
        linarith
      · obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
        have hmb : acc + (m : ℝ) * e < K := by
          rcases Nat.eq_zero_or_pos m with h0' | h0'
          · subst h0'
            simpa using hlt
          · have := hk3 m h0' (by omega)
            simpa [ts_g_zero_rate] using this
        rw [hm]
        push_cast
        nlinarith

theorem ts_step_thr {α K e acc : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (he : 0 ≤ e) (hle : e ≤ acc)
    (hzero : e = 0 → acc = 0) :
    (e + α) + (if K ≤ acc + (e + α) then K else 0) - ts_f α K =
      ts_D α K e acc - ts_D α K (if K ≤ acc + (e + α) then 0 else e + α)
        (if K ≤ acc + (e + α) then 0 else acc + (e + α)) := by
  have hacc : 0 ≤ acc := he.trans hle
  by_cases hspecial : α = 0 ∧ e = 0
  · obtain ⟨rfl, rfl⟩ := hspecial
    have hac : acc = 0 := hzero rfl
    subst hac
    have hnot : ¬ K ≤ (0 : ℝ) := not_le.2 hK
    simp [ts_D, ts_f_zero, hnot]
  · have hne := ts_k_exists hα hK he hacc hspecial
    by_cases hreset : K ≤ acc + (e + α)
    · simp only [hreset, if_true]
      rw [ts_D_zero hα hK]
      have hk1 : ts_k α K e acc = 1 := ts_k_eq le_rfl (by
        have : ts_g α 1 = α := by simp [ts_g]; ring
        rw [this]
        push_cast
        linarith) (fun n h1 h2 => absurd h2 (by omega))
      simp only [ts_D, hspecial, if_false, hk1]
      have hg1 : ts_g α 1 = α := by simp [ts_g]; ring
      simp only [ts_V, hg1]
      push_cast
      ring
    · simp only [hreset, if_false]
      have hlt : acc + (e + α) < K := not_le.1 hreset
      obtain ⟨hk1, hk2, hk3⟩ := ts_k_spec hne
      set k := ts_k α K e acc with hkdef
      have hk2' : 2 ≤ k := by
        by_contra hcon
        have hk : k = 1 := by omega
        rw [hk] at hk2
        have hg1 : ts_g α 1 = α := by simp [ts_g]; ring
        rw [hg1] at hk2
        push_cast at hk2
        linarith
      obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
      have hm1 : 1 ≤ m := by omega
      have hidentity : ∀ n : ℕ, acc + (e + α) + ts_g α n + n * (e + α)
          = acc + ts_g α (n + 1) + ((n + 1 : ℕ) : ℝ) * e := by
        intro n
        rw [ts_g_succ]
        push_cast
        ring
      have hk' : ts_k α K (e + α) (acc + (e + α)) = m := ts_k_eq hm1 (by
        rw [hidentity]
        rw [← hm]
        exact hk2) (fun n h1 h2 => by
        rw [hidentity]
        exact hk3 (n + 1) (by omega) (by omega))
      have hnext : ¬ (α = 0 ∧ e + α = 0) := by
        rintro ⟨h1, h2⟩
        apply hspecial
        refine ⟨h1, ?_⟩
        linarith
      simp only [ts_D, hspecial, hnext, if_false, hk', ← hkdef, hm]
      rw [ts_V_succ]
      ring

theorem ts_step_r {α K o : ℝ} (hα : 0 ≤ α) (hK : 0 < K) (ho : 0 ≤ o) (b : Bool) :
    ts_W α K o - ts_W α K (if b then 0 else o + α) ≤
      (o + α) + (if b then K else 0) - ts_f α K := by
  rcases hα.lt_or_eq with h | h
  · cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false]
      have : ts_W α K o - (o + α - ts_f α K) ≤ ts_W α K (o + α) := by
        refine ts_le_W h fun j => ?_
        have h1 := ts_W_le_V h hK ho (j + 1)
        rw [ts_V_succ] at h1
        linarith
      linarith
    | true =>
      simp only [if_true]
      rw [ts_W_zero hα hK]
      have h1 := ts_W_le_V h hK ho 1
      have hg1 : ts_g α 1 = α := by simp [ts_g]; ring
      simp only [ts_V, hg1] at h1
      push_cast at h1
      linarith
  · subst h
    rw [ts_f_zero]
    cases b with
    | false =>
      simp only [Bool.false_eq_true, if_false, add_zero]
      linarith
    | true =>
      simp only [if_true, add_zero]
      rw [ts_W_zero le_rfl hK]
      have := ts_W_le_K (α := 0) le_rfl hK ho
      linarith

noncomputable def ts_Hr (A : ℕ → ℝ) (R : ℕ → Bool) : ℕ → ℝ
  | 0 => 0
  | t + 1 => if R t = true then A t else ts_Hr A R t + A t

noncomputable def ts_state (A : ℕ → ℝ) (K : ℝ) : ℕ → ℝ × ℝ
  | 0 => (0, 0)
  | t + 1 =>
    if K ≤ (ts_state A K t).2 + (ts_state A K t).1 then (A t, 0)
    else ((ts_state A K t).1 + A t, (ts_state A K t).2 + (ts_state A K t).1)

theorem ts_core (T : ℕ) (hT : 2 ≤ T) (A : ℕ → ℝ) (hA : ∀ i, 0 ≤ A i) (K : ℝ) (hK : 0 < K)
    (R : ℕ → Bool) :
    ∑ t ∈ Finset.range T, ((ts_state A K t).1 +
        if K ≤ (ts_state A K t).2 + (ts_state A K t).1 then K else 0)
      ≤ ∑ t ∈ Finset.range T, (ts_Hr A R t + if R t = true then K else 0)
        + (2 * ((((Finset.Ico 1 (T - 1)).filter (fun t => A t ≠ A (t - 1))).card : ℝ) + 1) - 1) * K := by
  set H : ℕ → ℝ := fun t => (ts_state A K t).1 with hHdef
  set ac : ℕ → ℝ := fun t => (ts_state A K t).2 with hacdef
  set Hr : ℕ → ℝ := ts_Hr A R with hHrdef
  set e : ℕ → ℝ := fun t => if t = 0 then 0 else if K ≤ ac (t - 1) + H (t - 1) then 0 else H (t - 1)
    with hedef
  set o : ℕ → ℝ := fun t => if t = 0 then 0 else if R (t - 1) = true then 0 else Hr (t - 1)
    with hodef
  have hH0 : H 0 = 0 := rfl
  have hac0 : ac 0 = 0 := rfl
  have hHsucc : ∀ t, H (t + 1) = if K ≤ ac t + H t then A t else H t + A t := by
    intro t
    show (ts_state A K (t + 1)).1 = _
    rw [ts_state]
    split_ifs <;> rfl
  have hacsucc : ∀ t, ac (t + 1) = if K ≤ ac t + H t then 0 else ac t + H t := by
    intro t
    show (ts_state A K (t + 1)).2 = _
    rw [ts_state]
    split_ifs <;> rfl
  have he_succ : ∀ t, e (t + 1) = if K ≤ ac t + H t then 0 else H t := by
    intro t
    simp only [hedef, Nat.add_sub_cancel]
    simp
  have ho_succ : ∀ t, o (t + 1) = if R t = true then 0 else Hr t := by
    intro t
    simp only [hodef, Nat.add_sub_cancel]
    simp
  have hH_eq : ∀ t, H (t + 1) = e (t + 1) + A t := by
    intro t
    rw [hHsucc, he_succ]
    split_ifs <;> ring
  have hHrsucc : ∀ t, Hr (t + 1) = if R t = true then A t else Hr t + A t := by
    intro t
    show ts_Hr A R (t + 1) = _
    rw [ts_Hr]
  have hHr_eq : ∀ t, Hr (t + 1) = o (t + 1) + A t := by
    intro t
    rw [hHrsucc, ho_succ]
    split_ifs <;> ring
  have hHr_nonneg : ∀ t, 0 ≤ Hr t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      rw [hHrsucc]
      split_ifs
      · exact hA t
      · exact add_nonneg ih (hA t)
  have ho_nonneg : ∀ t, 0 ≤ o t := by
    intro t
    cases t with
    | zero => simp [hodef]
    | succ t =>
      rw [ho_succ]
      split_ifs
      · exact le_rfl
      · exact hHr_nonneg t
  have hinv : ∀ t, 1 ≤ t → 0 ≤ e t ∧ e t ≤ ac t ∧ ac t < K ∧ (e t = 0 → ac t = 0) := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base =>
      have hnot : ¬ K ≤ ac 0 + H 0 := by
        rw [hH0, hac0]
        simpa using hK
      have h1 : e 1 = 0 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, he_succ, if_neg hnot, hH0]
      have h2 : ac 1 = 0 := by
        rw [show (1 : ℕ) = 0 + 1 from rfl, hacsucc, if_neg hnot, hac0, hH0]
        ring
      rw [h1, h2]
      exact ⟨le_rfl, le_rfl, hK, fun _ => rfl⟩
    | succ t ht ih =>
      obtain ⟨i1, i2, i3, i4⟩ := ih
      obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
      have hHs : H (s + 1) = e (s + 1) + A s := hH_eq s
      have hHnn : 0 ≤ H (s + 1) := by rw [hHs]; exact add_nonneg i1 (hA s)
      have hacnn : 0 ≤ ac (s + 1) := i1.trans i2
      rw [he_succ (s + 1), hacsucc (s + 1)]
      split_ifs with hS
      · exact ⟨le_rfl, le_rfl, hK, fun _ => rfl⟩
      · refine ⟨hHnn, by linarith, not_le.1 hS, fun h0 => ?_⟩
        have he0 : e (s + 1) = 0 := by
          have := hA s
          linarith
        rw [i4 he0, h0]
        ring
  let Z : ℝ → ℕ → ℝ := fun γ s => ts_D γ K (e s) (ac s) - ts_W γ K (o s)
  -- the one-call inequality
  have hstep : ∀ s, (H (s + 1) + if K ≤ ac (s + 1) + H (s + 1) then K else 0)
      - (Hr (s + 1) + if R (s + 1) = true then K else 0)
      ≤ Z (A s) (s + 1) - Z (A s) (s + 2) := by
    intro s
    obtain ⟨i1, i2, i3, i4⟩ := hinv (s + 1) (by omega)
    have h1 := ts_step_thr (hA s) hK i1 i2 i4
    have h2 := ts_step_r (hA s) hK (ho_nonneg (s + 1)) (R (s + 1))
    have e1 : e (s + 2) = if K ≤ ac (s + 1) + (e (s + 1) + A s) then 0 else e (s + 1) + A s := by
      rw [show s + 2 = (s + 1) + 1 from rfl, he_succ, hH_eq s]
    have e2 : ac (s + 2) = if K ≤ ac (s + 1) + (e (s + 1) + A s) then 0
        else ac (s + 1) + (e (s + 1) + A s) := by
      rw [show s + 2 = (s + 1) + 1 from rfl, hacsucc, hH_eq s]
    have e3 : o (s + 2) = if R (s + 1) = true then 0 else o (s + 1) + A s := by
      rw [show s + 2 = (s + 1) + 1 from rfl, ho_succ, hHr_eq s]
    have h1' : H (s + 1) + (if K ≤ ac (s + 1) + H (s + 1) then K else 0) - ts_f (A s) K
        = ts_D (A s) K (e (s + 1)) (ac (s + 1)) - ts_D (A s) K (e (s + 2)) (ac (s + 2)) := by
      rw [e1, e2, hH_eq s]
      exact h1
    have h2' : ts_W (A s) K (o (s + 1)) - ts_W (A s) K (o (s + 2))
        ≤ Hr (s + 1) + (if R (s + 1) = true then K else 0) - ts_f (A s) K := by
      rw [e3, hHr_eq s]
      exact h2
    simp only [Z]
    linarith
  -- ranges of Z at a boundary
  have hband : ∀ s, 1 ≤ s → ∀ γ γ' : ℝ, 0 ≤ γ → 0 ≤ γ' → Z γ s - Z γ' s ≤ 2 * K := by
    intro s hs γ γ' hγ hγ'
    obtain ⟨i1, i2, i3, i4⟩ := hinv s hs
    have ho := ho_nonneg s
    have a1 := ts_W_D hγ hK i1 i2 i3 i4
    have a2 := ts_W_D hγ' hK i1 i2 i3 i4
    have b1 := ts_W_nonneg hγ hK i1
    have b2 := ts_W_nonneg hγ' hK ho
    have c1 := ts_W_le_K hγ hK i1
    have c2 := ts_W_le_K hγ' hK i1
    have d1 := ts_W_nonneg hγ hK ho
    have d2 := ts_W_le_K hγ' hK ho
    have d3 := ts_W_le_K hγ hK ho
    have d4 := ts_W_nonneg hγ' hK i1
    simp only [Z]
    rcases le_total (e s) (o s) with hle | hle
    · have m1 := ts_W_mono hγ hK i1 hle
      have m2 := ts_W_mono hγ' hK i1 hle
      linarith [a1.1, a1.2, a2.1, a2.2]
    · have m1 := ts_W_mono hγ hK ho hle
      have m2 := ts_W_mono hγ' hK ho hle
      linarith [a1.1, a1.2, a2.1, a2.2]
  let cnt : ℕ → ℕ := fun n => ((Finset.Ico 1 (n - 1)).filter (fun t => A t ≠ A (t - 1))).card
  let ρ : ℕ → ℝ := fun t => A (t - 1)
  have hρ : ∀ t, 0 ≤ ρ t := fun t => hA _
  have htele : ∀ n, 2 ≤ n → n ≤ T →
      ∑ t ∈ Finset.Ico 1 n, (Z (ρ t) t - Z (ρ t) (t + 1)) + Z (ρ (n - 1)) n
        ≤ Z (ρ 1) 1 + 2 * K * cnt n := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base =>
      intro _
      simp only [cnt]
      have : Finset.Ico 1 2 = {1} := by rfl
      rw [this, Finset.sum_singleton]
      have h2 : (Finset.Ico 1 (2 - 1)) = ∅ := by rfl
      rw [h2]
      simp
    | succ n hn ih =>
      intro hle
      have ih' := ih (by omega)
      rw [Finset.sum_Ico_succ_top (by omega)]
      have hn' : n + 1 - 1 = n := by omega
      rw [hn']
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hcnt : (cnt (m + 1 + 1) : ℝ) = cnt (m + 1) + (if A m ≠ A (m - 1) then 1 else 0) := by
        simp only [cnt]
        have e1 : m + 1 + 1 - 1 = m + 1 := by omega
        have e2 : m + 1 - 1 = m := by omega
        rw [e1, e2, Finset.card_filter, Finset.card_filter, Finset.sum_Ico_succ_top (by omega)]
        push_cast
        ring
      have hstepZ : Z (ρ (m + 1)) (m + 1) - Z (ρ (m + 1 - 1)) (m + 1)
          ≤ 2 * K * (if A m ≠ A (m - 1) then 1 else 0) := by
        by_cases hch : A m ≠ A (m - 1)
        · simp only [hch, ne_eq, not_false_eq_true, if_true, mul_one]
          exact hband (m + 1) (by omega) _ _ (hρ _) (hρ _)
        · have hρeq : ρ (m + 1) = ρ (m + 1 - 1) := by
            simp only [ρ, Nat.add_sub_cancel]
            exact not_not.1 hch
          rw [hρeq]
          simp [hch]
      rw [hcnt]
      have e4 : Z (ρ (m + 1 - 1)) (m + 1) = Z (ρ (m + 1 - 1)) (m + 1) := rfl
      simp only [Nat.add_sub_cancel] at ih' hstepZ ⊢
      nlinarith [ih', hstepZ]
  have hbase : Z (ρ 1) 1 = 0 := by
    have hρ1 := hρ 1
    have h1e : e 1 = 0 := by
      have : ¬ K ≤ ac 0 + H 0 := by rw [hH0, hac0]; simpa using hK
      rw [show (1 : ℕ) = 0 + 1 from rfl, he_succ, if_neg this, hH0]
    have h1a : ac 1 = 0 := by
      have : ¬ K ≤ ac 0 + H 0 := by rw [hH0, hac0]; simpa using hK
      rw [show (1 : ℕ) = 0 + 1 from rfl, hacsucc, if_neg this, hac0, hH0]
      ring
    have h1o : o 1 = 0 := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, ho_succ]
      split_ifs
      · rfl
      · rfl
    simp only [Z, h1e, h1a, h1o]
    rw [ts_D_zero hρ1 hK, ts_W_zero hρ1 hK]
    ring
  have hend : -K ≤ Z (ρ (T - 1)) T := by
    obtain ⟨i1, i2, i3, i4⟩ := hinv T (by omega)
    have hγ := hρ (T - 1)
    have a1 := (ts_W_D hγ hK i1 i2 i3 i4).1
    have b1 := ts_W_nonneg hγ hK i1
    have c1 := ts_W_le_K hγ hK (ho_nonneg T)
    simp only [Z]
    linarith
  have htot := htele T hT le_rfl
  rw [hbase] at htot
  -- sum over calls
  have hdiff : ∑ t ∈ Finset.Ico 1 T, ((H t + if K ≤ ac t + H t then K else 0)
      - (Hr t + if R t = true then K else 0))
      ≤ ∑ t ∈ Finset.Ico 1 T, (Z (ρ t) t - Z (ρ t) (t + 1)) := by
    refine Finset.sum_le_sum fun t ht => ?_
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by have := (Finset.mem_Ico.1 ht).1; omega⟩
    have := hstep s
    simp only [ρ, Nat.add_sub_cancel]
    exact this
  have hsplit1 : ∑ t ∈ Finset.range T, (H t + if K ≤ ac t + H t then K else 0)
      = (H 0 + if K ≤ ac 0 + H 0 then K else 0)
        + ∑ t ∈ Finset.Ico 1 T, (H t + if K ≤ ac t + H t then K else 0) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have hsplit2 : ∑ t ∈ Finset.range T, (Hr t + if R t = true then K else 0)
      = (Hr 0 + if R 0 = true then K else 0)
        + ∑ t ∈ Finset.Ico 1 T, (Hr t + if R t = true then K else 0) := by
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega)]
  have hfirst : (H 0 + if K ≤ ac 0 + H 0 then K else 0) ≤ (Hr 0 + if R 0 = true then K else 0) := by
    have hnot : ¬ K ≤ ac 0 + H 0 := by rw [hH0, hac0]; simpa using hK
    rw [if_neg hnot, hH0]
    have h0 : Hr 0 = 0 := rfl
    rw [h0]
    split_ifs <;> linarith
  have hgoal : (2 : ℝ) * ((cnt T : ℝ) + 1) - 1 = 2 * (cnt T : ℝ) + 1 := by ring
  have hdiff2 := Finset.sum_sub_distrib (s := Finset.Ico 1 T)
    (f := fun t => H t + if K ≤ ac t + H t then K else 0)
    (g := fun t => Hr t + if R t = true then K else 0)
  show ∑ t ∈ Finset.range T, (H t + if K ≤ ac t + H t then K else 0)
      ≤ ∑ t ∈ Finset.range T, (Hr t + if R t = true then K else 0)
        + (2 * ((cnt T : ℝ) + 1) - 1) * K
  rw [hsplit1, hsplit2, hgoal]
  rw [hdiff2] at hdiff
  nlinarith [hdiff, htot, hend, hfirst]

theorem threshold_schedule_additive_bound (T : ℕ) (hT : 2 ≤ T) (a : Fin (T - 1) → NNReal) (K : ℝ) (hK : 0 < K) (r : Fin T → Bool) : rent_or_buy_cost T a K (threshold_schedule T a K) ≤ rent_or_buy_cost T a K r + (2 * (rent_or_buy_num_runs T a : ℝ) - 1) * K := by
  let A : ℕ → ℝ := fun i => if h : i < T - 1 then ((a ⟨i, h⟩ : NNReal) : ℝ) else 0
  have hA : ∀ i, 0 ≤ A i := by
    intro i
    simp only [A]
    split_ifs
    · exact NNReal.coe_nonneg _
    · exact le_rfl
  have hAval : ∀ i (h : i < T - 1), A i = ((a ⟨i, h⟩ : NNReal) : ℝ) := fun i h => by
    simp only [A, dif_pos h]
  let mkR : (Fin T → Bool) → ℕ → Bool := fun s t => if h : t < T then s ⟨t, h⟩ else false
  have hmkR : ∀ (s : Fin T → Bool) t (h : t < T), mkR s t = s ⟨t, h⟩ := fun s t h => by
    simp only [mkR, dif_pos h]
  -- histories of a schedule
  have hhist : ∀ (s : Fin T → Bool) t (h : t < T),
      ((schedule_history T a s ⟨t, h⟩ : NNReal) : ℝ) = ts_Hr A (mkR s) t := by
    intro s t
    induction t with
    | zero =>
      intro h
      rw [ts_Hr, schedule_history]
      simp
    | succ t ih =>
      intro h
      have ht : t < T - 1 := by omega
      rw [ts_Hr, schedule_history, hmkR s t (by omega), hAval t ht]
      by_cases hs : s ⟨t, by omega⟩ = true
      · simp [hs]
      · simp only [hs, if_false, Bool.false_eq_true]
        rw [NNReal.coe_add, ih (by omega)]
  -- states of the threshold rule
  have hstate : ∀ t (h : t < T),
      (((threshold_state T a K ⟨t, h⟩).1 : NNReal) : ℝ) = (ts_state A K t).1 ∧
      (((threshold_state T a K ⟨t, h⟩).2 : NNReal) : ℝ) = (ts_state A K t).2 := by
    intro t
    induction t with
    | zero =>
      intro h
      rw [threshold_state, ts_state]
      simp
    | succ t ih =>
      intro h
      obtain ⟨i1, i2⟩ := ih (by omega)
      have ht : t < T - 1 := by omega
      rw [threshold_state, ts_state]
      dsimp only
      rw [← i1, ← i2]
      by_cases hc : K ≤ ((threshold_state T a K ⟨t, by omega⟩).2 : ℝ) + ((threshold_state T a K ⟨t, by omega⟩).1 : ℝ)
      · simp only [hc, if_true]
        exact ⟨(hAval t ht).symm, rfl⟩
      · simp only [hc, if_false]
        constructor
        · rw [NNReal.coe_add, hAval t ht]
        · rw [NNReal.coe_add]
  have hdecide : ∀ t (h : t < T), mkR (threshold_schedule T a K) t =
      decide (K ≤ (ts_state A K t).2 + (ts_state A K t).1) := by
    intro t h
    rw [hmkR _ t h]
    obtain ⟨i1, i2⟩ := hstate t h
    rw [← i1, ← i2]
    simp only [threshold_schedule]
  have hthr : ∀ t (h : t < T), ts_Hr A (mkR (threshold_schedule T a K)) t = (ts_state A K t).1 := by
    intro t
    induction t with
    | zero => intro h; rw [ts_Hr, ts_state]
    | succ t ih =>
      intro h
      rw [ts_Hr, hdecide t (by omega), ts_state, ih (by omega)]
      by_cases hc : K ≤ (ts_state A K t).2 + (ts_state A K t).1
      · simp [hc]
      · simp [hc]
  have hcost : ∀ s : Fin T → Bool, rent_or_buy_cost T a K s
      = ∑ t ∈ Finset.range T, (ts_Hr A (mkR s) t + if mkR s t = true then K else 0) := by
    intro s
    rw [Finset.sum_range]
    unfold rent_or_buy_cost
    refine Finset.sum_congr rfl fun t _ => ?_
    have h1 := hhist s t.val t.isLt
    have h2 := hmkR s t.val t.isLt
    simp only [Fin.eta] at h1 h2
    rw [h1, h2]
  have hcard : rent_or_buy_num_runs T a
      = 1 + ((Finset.Ico 1 (T - 1)).filter (fun t => A t ≠ A (t - 1))).card := by
    unfold rent_or_buy_num_runs
    rw [dif_pos hT]
    congr 1
    refine Finset.card_bij (fun i _ => i.val + 1) ?_ ?_ ?_
    · intro i hi
      have hne := (Finset.mem_filter.1 hi).2
      refine Finset.mem_filter.2 ⟨Finset.mem_Ico.2 ⟨by omega, by have := i.isLt; omega⟩, ?_⟩
      have h1 : i.val + 1 < T - 1 := by have := i.isLt; omega
      have h2 : i.val < T - 1 := by have := i.isLt; omega
      simp only [Nat.add_sub_cancel]
      rw [hAval _ h1, hAval _ h2]
      intro he
      exact hne (NNReal.coe_injective he)
    · intro i _ j _ h
      exact Fin.ext (by simpa using h)
    · intro t ht
      obtain ⟨ht1, ht2⟩ := Finset.mem_filter.1 ht
      obtain ⟨h1, h2⟩ := Finset.mem_Ico.1 ht1
      have hi : t - 1 < T - 2 := by omega
      refine ⟨⟨t - 1, hi⟩, ?_, by simp; omega⟩
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, fun he => ht2 ?_⟩
      have h3 : t < T - 1 := h2
      have h4 : t - 1 < T - 1 := by omega
      have e1 : (⟨(⟨t - 1, hi⟩ : Fin (T - 2)).val + 1, by simp; omega⟩ : Fin (T - 1)) = ⟨t, h3⟩ :=
        Fin.ext (by simp; omega)
      have e2 : (⟨(⟨t - 1, hi⟩ : Fin (T - 2)).val, by simp; omega⟩ : Fin (T - 1)) = ⟨t - 1, h4⟩ :=
        Fin.ext rfl
      rw [e1, e2] at he
      rw [hAval _ h3, hAval _ h4, he]
  have hcore := ts_core T hT A hA K hK (mkR r)
  rw [hcost r, hcost (threshold_schedule T a K)]
  have hthrsum : ∑ t ∈ Finset.range T, (ts_Hr A (mkR (threshold_schedule T a K)) t +
      if mkR (threshold_schedule T a K) t = true then K else 0)
      = ∑ t ∈ Finset.range T, ((ts_state A K t).1 +
        if K ≤ (ts_state A K t).2 + (ts_state A K t).1 then K else 0) := by
    refine Finset.sum_congr rfl fun t ht => ?_
    have htT := Finset.mem_range.1 ht
    rw [hthr t htT, hdecide t htT]
    simp
  rw [hthrsum, hcard]
  push_cast
  linarith [hcore]
