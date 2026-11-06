import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCostLe
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.F

/-!
# probabilistic_serial_line_distortion_ge_sharp

Topic: social_choice   Node: 264f72a8196a

Provenance: original. Related work: OP-1158; arXiv:2611.05777 (footnote to Theorem 2, Figure 1) gets a cost of at least n/2 against OPT about 1 from a line cascade, i.e. ratio about n/2

Sharpness half of OP-1158: for every n >= 2 and every real c < n there are n agents and n items at real positions with positive minimum perfect-matching cost OPT such that, for every ranking profile by distance (any tie-breaking), the probabilistic serial cost exceeds c * OPT. So the supremum of PS/OPT over line instances is at least n.
-/

theorem ps_cascade_phase_eq {n : ℕ} (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (ch : Fin n → Fin n) (τ : ℝ)
    (heats : ∀ i j, (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') ↔ j = ch i)
    (j0 : Fin n) (hj0 : 0 < (Finset.univ.filter (fun i => ch i = j0)).card)
    (hτ : s.1 j0 / ((Finset.univ.filter (fun i => ch i = j0)).card : ℝ) = τ)
    (hle : ∀ j, 0 < (Finset.univ.filter (fun i => ch i = j)).card →
      τ ≤ s.1 j / ((Finset.univ.filter (fun i => ch i = j)).card : ℝ)) :
    probabilistic_serial_phase n pref s =
      (fun j => s.1 j - τ * ((Finset.univ.filter (fun i => ch i = j)).card : ℝ),
       fun i j => s.2 i j + if j = ch i then τ else 0) := by
  classical
  have hcnt : ∀ j, (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card
      = (Finset.univ.filter (fun i => ch i = j)).card := by
    intro j
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [heats i j, eq_comm]
  have hS : (Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card)).Nonempty :=
    ⟨j0, by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcnt]; exact hj0⟩
  have ht : (Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card)).inf' hS
      (fun j => s.1 j / ((Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card : ℝ)) = τ := by
    apply le_antisymm
    · rw [← hτ, ← hcnt]
      exact Finset.inf'_le _ (by simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcnt]; exact hj0)
    · apply Finset.le_inf'
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hcnt] at hj
      rw [hcnt]
      exact hle j hj
  unfold probabilistic_serial_phase
  simp only
  rw [dif_pos hS]
  rw [ht]
  ext j
  · simp only [hcnt]
  · simp only [heats]

theorem ps_cascade_eats_iff {n : ℕ} (a b : Fin n → ℝ) (pref : Fin n → Equiv.Perm (Fin n))
    (hp : is_line_distance_preference_profile a b pref) (P : Fin n → Prop) (i c : Fin n)
    (hc : P c) (hmin : ∀ j, P j → j ≠ c → |a i - b c| < |a i - b j|) (j : Fin n) :
    (P j ∧ ∀ j', P j' → (pref i).symm j ≤ (pref i).symm j') ↔ j = c := by
  constructor
  · rintro ⟨hj, hall⟩
    by_contra hne
    have h1 := hall c hc
    have h2 : (pref i).symm j < (pref i).symm c := by
      rcases h1.lt_or_eq with h | h
      · exact h
      · exact absurd ((pref i).symm.injective h) hne
    have h3 := hp i _ _ h2
    simp only [Equiv.apply_symm_apply] at h3
    exact absurd (hmin j hj hne) (not_lt.mpr h3)
  · rintro rfl
    refine ⟨hc, fun j' hj' => ?_⟩
    by_contra hlt
    rw [not_le] at hlt
    have h3 := hp i _ _ hlt
    simp only [Equiv.apply_symm_apply] at h3
    have hne : j' ≠ j := by
      rintro rfl
      exact lt_irrefl _ hlt
    exact absurd (hmin j' hj' hne) (not_lt.mpr h3)

theorem ps_cascade_cost_step {n : ℕ} (d : Fin n → Fin n → ℝ) (X : Fin n → Fin n → ℝ)
    (ch : Fin n → Fin n) (τ : ℝ) :
    ∑ i, ∑ j, (X i j + if j = ch i then τ else 0) * d i j
      = ∑ i, ∑ j, X i j * d i j + τ * ∑ i, d i (ch i) := by
  simp only [add_mul, Finset.sum_add_distrib, ite_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true, Finset.mul_sum]

theorem ps_cascade_step {n : ℕ} (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (pref : Fin n → Equiv.Perm (Fin n))
    (hp : is_line_distance_preference_profile (fun i : Fin n => (2:ℝ) ^ (i:ℕ))
      (fun j : Fin n => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) pref)
    (k : ℕ) (hk : k + 2 ≤ n) (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ))
    (hs : s.1 = fun j : Fin n => if (j:ℕ) = 0 then ((k:ℝ) + 1) / 2 ^ k else if (j:ℕ) ≤ k then 0 else 1 / 2 ^ k) :
    (probabilistic_serial_phase n pref s).1 = (fun j : Fin n => if (j:ℕ) = 0 then (((k + 1 : ℕ) : ℝ) + 1) / 2 ^ (k + 1)
        else if (j:ℕ) ≤ k + 1 then 0 else 1 / 2 ^ (k + 1)) ∧
    ∑ i, ∑ j, s.2 i j * |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| + (1 - 1 / 2 ^ (k + 1))
      ≤ ∑ i, ∑ j, (probabilistic_serial_phase n pref s).2 i j *
          |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| := by
  classical
  let ch : Fin n → Fin n := fun i =>
    ⟨if (i:ℕ) < k then 0 else if (i:ℕ) = k then k + 1 else i, by
      have := i.isLt; split_ifs <;> omega⟩
  have hchv : ∀ i, (ch i : ℕ) = if (i:ℕ) < k then 0 else if (i:ℕ) = k then k + 1 else i :=
    fun i => rfl
  have hpk : (0:ℝ) < 2 ^ k := by positivity
  have hpos : ∀ j : Fin n, 0 < s.1 j ↔ ((j:ℕ) = 0 ∨ k < j) := by
    intro j
    rw [hs]
    simp only
    split_ifs with h1 h2
    · simp only [h1, true_or, iff_true]; positivity
    · simp only [lt_irrefl, false_iff, not_or]; omega
    · simp only [h1, false_or]
      exact ⟨fun _ => by omega, fun _ => by positivity⟩
  have hd0 : ∀ m : ℕ, |(2:ℝ) ^ m - (-δ)| = 2 ^ m + δ := by
    intro m
    have : (0:ℝ) < 2 ^ m := by positivity
    rw [abs_of_pos (by linarith)]; ring
  have hdlt : ∀ m p : ℕ, m < p → |(2:ℝ) ^ m - 2 ^ p| = 2 ^ p - 2 ^ m := by
    intro m p h
    rw [abs_of_neg, neg_sub]
    have := pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) h
    linarith
  have hdgt : ∀ m p : ℕ, p < m → |(2:ℝ) ^ m - 2 ^ p| = 2 ^ m - 2 ^ p := by
    intro m p h
    rw [abs_of_pos]
    have := pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) h
    linarith
  have h2le : ∀ m p : ℕ, m + 2 ≤ p → 4 * (2:ℝ) ^ m ≤ 2 ^ p := by
    intro m p h
    have := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) h
    rw [pow_add] at this; linarith
  have hmin : ∀ i j, 0 < s.1 j → j ≠ ch i →
      |(2:ℝ) ^ (i:ℕ) - (if ((ch i : Fin n):ℕ) = 0 then -δ else (2:ℝ) ^ ((ch i : Fin n):ℕ))|
        < |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| := by
    intro i j hj hne
    rw [hpos] at hj
    rw [Ne, Fin.ext_iff, hchv] at hne
    have hi1 : (1:ℝ) ≤ 2 ^ (i:ℕ) := one_le_pow₀ (by norm_num)
    rw [hchv]
    by_cases hik : (i:ℕ) < k
    · rw [if_pos hik] at hne ⊢
      rw [if_pos rfl, hd0]
      have hj0 : (j:ℕ) ≠ 0 := hne
      rw [if_neg hj0, hdlt _ _ (by omega)]
      have := h2le (i:ℕ) j (by omega)
      linarith
    · rw [if_neg hik] at hne ⊢
      by_cases hik' : (i:ℕ) = k
      · rw [if_pos hik'] at hne ⊢
        rw [if_neg (by omega), hdlt _ _ (by omega), pow_succ]
        have hik2 : (2:ℝ) ^ (i:ℕ) = 2 ^ k := by rw [hik']
        by_cases hj0 : (j:ℕ) = 0
        · rw [if_pos hj0, hd0]; linarith
        · rw [if_neg hj0, hdlt _ _ (by omega)]
          have := h2le (i:ℕ) j (by omega)
          linarith
      · rw [if_neg hik'] at hne ⊢
        rw [if_neg (by omega), sub_self, abs_zero]
        by_cases hj0 : (j:ℕ) = 0
        · rw [if_pos hj0, hd0]; positivity
        · rw [if_neg hj0]
          rcases lt_or_gt_of_ne hne with h | h
          · rw [hdgt _ _ h]
            have := pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) h
            linarith
          · rw [hdlt _ _ h]
            have := pow_lt_pow_right₀ (by norm_num : (1:ℝ) < 2) h
            linarith
  have hc : ∀ i, 0 < s.1 (ch i) := by
    intro i; rw [hpos, hchv]; split_ifs <;> omega
  have heats : ∀ i j, (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') ↔
      j = ch i := fun i j =>
    ps_cascade_eats_iff _ _ pref hp (fun j => 0 < s.1 j) i (ch i) (hc i)
      (fun j hj hne => hmin i j hj hne) j
  have hcard : ∀ j : Fin n, (Finset.univ.filter (fun i => ch i = j)).card =
      if (j:ℕ) = 0 then k else if (j:ℕ) ≤ k then 0 else if (j:ℕ) = k + 1 then 2 else 1 := by
    intro j
    split_ifs with h0 h1 h2
    · have : Finset.univ.filter (fun i => ch i = j) =
          Finset.univ.filter (fun i : Fin n => (i:ℕ) < k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff, hchv, h0]
        split_ifs <;> (constructor <;> intro h <;> first | exact h.elim | omega)
      rw [this, Fin.card_filter_val_lt]; omega
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h
      rw [Fin.ext_iff, hchv] at h
      split_ifs at h <;> omega
    · have : Finset.univ.filter (fun i => ch i = j) = {⟨k, by omega⟩, j} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
          Finset.mem_singleton, Fin.ext_iff, hchv]
        split_ifs <;> (constructor <;> intro h <;> first | exact h.elim | omega)
      rw [this, Finset.card_pair]
      rw [Ne, Fin.ext_iff]
      show ¬ (k = (j:ℕ))
      omega
    · have : Finset.univ.filter (fun i => ch i = j) = {j} := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton, Fin.ext_iff, hchv]
        split_ifs <;> (constructor <;> intro h <;> first | exact h.elim | omega)
      rw [this, Finset.card_singleton]
  have hk1 : k + 1 < n := by omega
  have hj0 : 0 < (Finset.univ.filter (fun i => ch i = ⟨k + 1, hk1⟩)).card := by
    rw [hcard]
    show 0 < if k + 1 = 0 then k else if k + 1 ≤ k then 0 else if k + 1 = k + 1 then 2 else 1
    rw [if_neg (by omega), if_neg (by omega), if_pos rfl]; norm_num
  have hτ : s.1 ⟨k + 1, hk1⟩ / ((Finset.univ.filter (fun i => ch i = ⟨k + 1, hk1⟩)).card : ℝ)
      = 1 / 2 ^ (k + 1) := by
    rw [hcard, hs]
    show (if k + 1 = 0 then ((k:ℝ) + 1) / 2 ^ k else if k + 1 ≤ k then 0 else 1 / 2 ^ k) /
      (((if k + 1 = 0 then k else if k + 1 ≤ k then 0 else if k + 1 = k + 1 then 2 else 1 : ℕ)) : ℝ)
      = 1 / 2 ^ (k + 1)
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl,
      pow_succ]
    push_cast
    field_simp
  have hle : ∀ j, 0 < (Finset.univ.filter (fun i => ch i = j)).card →
      1 / 2 ^ (k + 1) ≤ s.1 j / ((Finset.univ.filter (fun i => ch i = j)).card : ℝ) := by
    intro j hj
    rw [hcard] at hj ⊢
    rw [hs]
    simp only
    split_ifs at hj ⊢ with h0 h1 h2
    · have hk0 : (0:ℝ) < k := by exact_mod_cast hj
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity), pow_succ]
      nlinarith [mul_pos hpk hk0]
    · omega
    · push_cast
      rw [div_div, pow_succ]
    · push_cast
      rw [div_one, pow_succ]
      apply div_le_div_of_nonneg_left (by norm_num) hpk
      linarith
  rw [ps_cascade_phase_eq pref s ch (1 / 2 ^ (k + 1)) heats ⟨k + 1, hk1⟩ hj0 hτ hle]
  constructor
  · funext j
    simp only
    rw [hcard, hs]
    simp only
    split_ifs <;> first | omega | (push_cast; field_simp; ring)
  · simp only
    have hstep := ps_cascade_cost_step
      (fun (i j : Fin n) => |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))|) s.2 ch
      (1 / 2 ^ (k + 1))
    try simp only at hstep
    rw [hstep]
    have hsum : (2:ℝ) ^ (k + 1) - 1 ≤ ∑ i : Fin n,
        |(2:ℝ) ^ (i:ℕ) - (if ((ch i : Fin n):ℕ) = 0 then -δ else (2:ℝ) ^ ((ch i : Fin n):ℕ))| := by
      let F : ℕ → ℝ := fun m => if m < k then 2 ^ m else if m = k then 2 ^ k else 0
      have hF : ∀ i : Fin n, F i ≤
          |(2:ℝ) ^ (i:ℕ) - (if ((ch i : Fin n):ℕ) = 0 then -δ else (2:ℝ) ^ ((ch i : Fin n):ℕ))| := by
        intro i
        simp only [F]
        rw [hchv]
        split_ifs with h1 h2 h3 h4 h5
        · rw [hd0]; linarith
        · exact absurd rfl h2
        · exact h4.elim
        · rw [hdlt _ _ (by omega), pow_succ, h3]; linarith
        · exact abs_nonneg _
        · exact abs_nonneg _
      have hF0 : ∀ m, 0 ≤ F m := by
        intro m; simp only [F]; split_ifs <;> positivity
      calc (2:ℝ) ^ (k + 1) - 1 = ∑ m ∈ Finset.range (k + 1), F m := by
            rw [Finset.sum_range_succ]
            have : ∑ m ∈ Finset.range k, F m = ∑ m ∈ Finset.range k, (2:ℝ) ^ m := by
              apply Finset.sum_congr rfl
              intro m hm
              rw [Finset.mem_range] at hm
              simp only [F, if_pos hm]
            rw [this, geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
            simp only [F, lt_irrefl, ↓reduceIte]
            rw [pow_succ]; ring
        _ ≤ ∑ m ∈ Finset.range n, F m :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
              (fun m _ _ => hF0 m)
        _ = ∑ i : Fin n, F i := (Fin.sum_univ_eq_sum_range F n).symm
        _ ≤ _ := Finset.sum_le_sum (fun i _ => hF i)
    have hτ0 : (0:ℝ) ≤ 1 / 2 ^ (k + 1) := by positivity
    have e : 1 / 2 ^ (k + 1) * ((2:ℝ) ^ (k + 1) - 1) = 1 - 1 / 2 ^ (k + 1) := by
      field_simp
    have := mul_le_mul_of_nonneg_left hsum hτ0
    linarith


theorem ps_cascade_last {m : ℕ} (δ : ℝ) (hδ0 : 0 < δ)
    (pref : Fin (m + 1) → Equiv.Perm (Fin (m + 1)))
    (s : (Fin (m + 1) → ℝ) × (Fin (m + 1) → Fin (m + 1) → ℝ))
    (hs : s.1 = fun j : Fin (m + 1) => if (j:ℕ) = 0 then ((m:ℝ) + 1) / 2 ^ m
      else if (j:ℕ) ≤ m then 0 else 1 / 2 ^ m) :
    ∑ i, ∑ j, s.2 i j * |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| + (2 - 1 / 2 ^ m)
      ≤ ∑ i, ∑ j, (probabilistic_serial_phase (m + 1) pref s).2 i j *
          |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| := by
  classical
  have hpm : (0:ℝ) < 2 ^ m := by positivity
  have hpos : ∀ j : Fin (m + 1), 0 < s.1 j ↔ j = 0 := by
    intro j
    rw [hs, Fin.ext_iff]
    simp only [Fin.val_zero]
    have := j.isLt
    split_ifs with h1 h2
    · simp only [h1, iff_true]; positivity
    · simp only [lt_irrefl, false_iff]; exact h1
    · omega
  have heats : ∀ i j, (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') ↔
      j = (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i := by
    intro i j
    simp only [hpos]
    constructor
    · exact fun h => h.1
    · rintro rfl
      exact ⟨rfl, fun j' hj' => by rw [hj']⟩
  have hcard : ∀ j : Fin (m + 1),
      (Finset.univ.filter (fun i => (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i = j)).card
        = if j = 0 then m + 1 else 0 := by
    intro j
    split_ifs with h
    · subst h; simp
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ h'; exact h h'.symm
  have hle : ∀ j, 0 < (Finset.univ.filter (fun i => (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i = j)).card →
      1 / 2 ^ m ≤ s.1 j / ((Finset.univ.filter
        (fun i => (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i = j)).card : ℝ) := by
    intro j hj
    rw [hcard] at hj ⊢
    split_ifs at hj ⊢ with h
    · subst h
      rw [hs]
      simp only [Fin.val_zero, ↓reduceIte]
      push_cast
      rw [div_div, mul_comm, ← div_div, div_self (by positivity)]
    · omega
  have hj0 : 0 < (Finset.univ.filter (fun i => (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i = 0)).card := by
    rw [hcard]; simp
  have hτ : s.1 0 / ((Finset.univ.filter (fun i => (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) i = 0)).card : ℝ)
      = 1 / 2 ^ m := by
    apply le_antisymm
    · rw [hcard, hs]
      simp only [Fin.val_zero, ↓reduceIte]
      push_cast
      rw [div_div, mul_comm, ← div_div, div_self (by positivity)]
    · exact hle 0 hj0
  rw [ps_cascade_phase_eq pref s (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) (1 / 2 ^ m) heats 0 hj0 hτ hle]
  simp only
  have hstep := ps_cascade_cost_step
    (fun (i j : Fin (m + 1)) => |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))|) s.2
    (fun _ : Fin (m + 1) => (0 : Fin (m + 1))) (1 / 2 ^ m)
  try simp only at hstep
  rw [hstep]
  have hsum : (2:ℝ) ^ (m + 1) - 1 ≤ ∑ i : Fin (m + 1),
      |(2:ℝ) ^ (i:ℕ) - (if ((0 : Fin (m + 1)) : ℕ) = 0 then -δ else (2:ℝ) ^ ((0 : Fin (m + 1)) : ℕ))| := by
    simp only [Fin.val_zero, ↓reduceIte]
    have : ∀ i : Fin (m + 1), |(2:ℝ) ^ (i:ℕ) - -δ| = 2 ^ (i:ℕ) + δ := by
      intro i
      have : (0:ℝ) < 2 ^ (i:ℕ) := by positivity
      rw [abs_of_pos (by linarith)]; ring
    simp only [this, Finset.sum_add_distrib]
    rw [Fin.sum_univ_eq_sum_range (fun i => (2:ℝ) ^ i) (m + 1),
      geom_sum_eq (by norm_num : (2:ℝ) ≠ 1)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (0:ℝ) ≤ ((m:ℝ) + 1) * δ := by positivity
    push_cast
    linarith
  have hτ0 : (0:ℝ) ≤ 1 / 2 ^ m := by positivity
  have e : 1 / 2 ^ m * ((2:ℝ) ^ (m + 1) - 1) = 2 - 1 / 2 ^ m := by
    rw [pow_succ]; field_simp
  have := mul_le_mul_of_nonneg_left hsum hτ0
  linarith

theorem ps_cascade_iter {n : ℕ} (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (pref : Fin n → Equiv.Perm (Fin n))
    (hp : is_line_distance_preference_profile (fun i : Fin n => (2:ℝ) ^ (i:ℕ))
      (fun j : Fin n => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) pref)
    (k : ℕ) (hk : k + 1 ≤ n) :
    ((probabilistic_serial_phase n pref)^[k] (fun _ => 1, fun _ _ => 0)).1 =
      (fun j : Fin n => if (j:ℕ) = 0 then ((k:ℝ) + 1) / 2 ^ k else if (j:ℕ) ≤ k then 0 else 1 / 2 ^ k) ∧
    (k:ℝ) - 1 + 1 / 2 ^ k ≤ ∑ i, ∑ j,
      ((probabilistic_serial_phase n pref)^[k] (fun _ => 1, fun _ _ => 0)).2 i j *
        |(2:ℝ) ^ (i:ℕ) - (if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ))| := by
  induction k with
  | zero =>
    simp only [Function.iterate_zero, id, Nat.cast_zero, pow_zero, zero_add, div_one,
      nonpos_iff_eq_zero, zero_mul, Finset.sum_const_zero]
    refine ⟨?_, by norm_num⟩
    funext j
    split_ifs <;> rfl
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [Function.iterate_succ_apply']
    obtain ⟨h3, h4⟩ := ps_cascade_step δ hδ0 hδ1 pref hp k (by omega) _ h1
    refine ⟨h3, ?_⟩
    have e : (1:ℝ) / 2 ^ k = 2 * (1 / 2 ^ (k + 1)) := by rw [pow_succ]; field_simp
    push_cast
    linarith

theorem probabilistic_serial_line_distortion_ge_sharp (n : ℕ) (hn : 2 ≤ n) (c : ℝ) (hc : c < n) :
    ∃ a b : Fin n → ℝ, 0 < line_min_matching_cost a b ∧
      ∀ pref, is_line_distance_preference_profile a b pref →
        c * line_min_matching_cost a b < probabilistic_serial_line_cost a b pref := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hn0 : (0:ℝ) < (m:ℝ) + 1 := by positivity
  set δ : ℝ := min (1 / 2) ((((m + 1 : ℕ) : ℝ) - c) / (2 * (((m + 1 : ℕ) : ℝ) + 1))) with hδ
  have hnc : (0:ℝ) < ((m + 1 : ℕ) : ℝ) - c := by linarith
  have hδ0 : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  have hδ2 : δ ≤ (((m + 1 : ℕ) : ℝ) - c) / (2 * (((m + 1 : ℕ) : ℝ) + 1)) := min_le_right _ _
  refine ⟨fun i => (2:ℝ) ^ (i:ℕ), fun j => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ), ?_, ?_⟩
  · unfold line_min_matching_cost
    rw [Finset.lt_inf'_iff]
    intro σ _
    have h0 : (0:ℝ) < |(2:ℝ) ^ ((0 : Fin (m + 1)) : ℕ) -
        (if ((σ 0 : Fin (m + 1)) : ℕ) = 0 then -δ else (2:ℝ) ^ ((σ 0 : Fin (m + 1)) : ℕ))| := by
      simp only [Fin.val_zero, pow_zero]
      split_ifs with h
      · rw [abs_of_pos (by linarith)]; linarith
      · have : (2:ℝ) ≤ 2 ^ ((σ 0 : Fin (m + 1)) : ℕ) := by
          calc (2:ℝ) = 2 ^ 1 := by norm_num
            _ ≤ _ := pow_le_pow_right₀ (by norm_num) (by omega)
        rw [abs_of_neg (by linarith)]; linarith
    exact lt_of_lt_of_le h0 (Finset.single_le_sum (f := fun i : Fin (m + 1) =>
      |(2:ℝ) ^ (i:ℕ) - (if ((σ i : Fin (m + 1)) : ℕ) = 0 then -δ else (2:ℝ) ^ ((σ i : Fin (m + 1)) : ℕ))|)
      (fun i _ => abs_nonneg _) (Finset.mem_univ 0))
  · intro pref hp
    have hopt : line_min_matching_cost (fun i : Fin (m + 1) => (2:ℝ) ^ (i:ℕ))
        (fun j => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) ≤ 1 + δ := by
      refine le_trans (line_min_matching_cost_le _ _ (Equiv.refl _)) (le_of_eq ?_)
      simp only [Equiv.refl_apply]
      rw [Finset.sum_eq_single (0 : Fin (m + 1))]
      · simp only [Fin.val_zero, ↓reduceIte, pow_zero]
        rw [abs_of_pos (by linarith)]; ring
      · intro i _ hi
        have : (i:ℕ) ≠ 0 := fun h => hi (Fin.ext h)
        simp only [this, ↓reduceIte, sub_self, abs_zero]
      · intro h; exact absurd (Finset.mem_univ _) h
    have hopt0 : 0 ≤ line_min_matching_cost (fun i : Fin (m + 1) => (2:ℝ) ^ (i:ℕ))
        (fun j => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) := by
      unfold line_min_matching_cost
      rw [Finset.le_inf'_iff]
      intro σ _
      exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
    have hps : ((m + 1 : ℕ) : ℝ) ≤ probabilistic_serial_line_cost
        (fun i : Fin (m + 1) => (2:ℝ) ^ (i:ℕ)) (fun j => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) pref := by
      unfold probabilistic_serial_line_cost probabilistic_serial_fractional_assignment
      rw [Function.iterate_succ_apply']
      obtain ⟨h1, h2⟩ := ps_cascade_iter δ hδ0 hδ1 pref hp m (by omega)
      have h3 := ps_cascade_last δ hδ0 pref _ h1
      push_cast
      linarith
    by_cases hc0 : c ≤ 0
    · have : c * line_min_matching_cost (fun i : Fin (m + 1) => (2:ℝ) ^ (i:ℕ))
          (fun j => if (j:ℕ) = 0 then -δ else (2:ℝ) ^ (j:ℕ)) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hc0 hopt0
      have : (0:ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      linarith
    · rw [not_le] at hc0
      have h1 := mul_le_mul_of_nonneg_left hopt hc0.le
      have h2 : c * δ < ((m + 1 : ℕ) : ℝ) - c := by
        have hpos2 : (0:ℝ) < 2 * (((m + 1 : ℕ) : ℝ) + 1) := by positivity
        have h3 : c * δ ≤ c * ((((m + 1 : ℕ) : ℝ) - c) / (2 * (((m + 1 : ℕ) : ℝ) + 1))) :=
          mul_le_mul_of_nonneg_left hδ2 hc0.le
        have h4 : c * ((((m + 1 : ℕ) : ℝ) - c) / (2 * (((m + 1 : ℕ) : ℝ) + 1)))
            < ((m + 1 : ℕ) : ℝ) - c := by
          rw [mul_div_assoc', div_lt_iff₀ hpos2]
          have : c < 2 * (((m + 1 : ℕ) : ℝ) + 1) := by linarith
          nlinarith
        linarith
      nlinarith
