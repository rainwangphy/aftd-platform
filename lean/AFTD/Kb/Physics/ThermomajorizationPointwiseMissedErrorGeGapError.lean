import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedError
import AFTD.Kb.Physics.ThermomajorizationProbeGapError
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_pointwise_missed_error_ge_gap_error

Topic: quantum_mechanics   Node: a3de305303fc

Provenance: helper lemma. arXiv:2610.35433, Population capacity and the geometry of thermomajorization

For any dimension n ≥ 2, probe set F ⊆ {1,...,n-1}, and unprobed rank j ∈ {1,...,n-1} \ F, the pointwise missed error thermomajorization_pointwise_missed_error n F j is bounded below by thermomajorization_probe_gap_error a b j, where a = max({0} ∪ {k ∈ F : k < j}) and b = min({n} ∪ {k ∈ F : k > j}).
-/

theorem thermomajorization_pointwise_missed_error_ge_gap_error_card_fin_filter_lt (n j : ℕ) (hj : j ≤ n) :
    (Finset.filter (fun (i : Fin n) => (i : ℕ) < j) Finset.univ).card = j := by
  obtain hj_lt | rfl := lt_or_eq_of_le hj
  · have h_set : Finset.filter (fun (i : Fin n) => (i : ℕ) < j) Finset.univ = Finset.Iio ⟨j, hj_lt⟩ := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio, Fin.lt_def]
    rw [h_set, Fin.card_Iio]
  · have h_set : Finset.filter (fun (i : Fin j) => (i : ℕ) < j) Finset.univ = Finset.univ := by
      ext ⟨i, hi⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, hi]
    rw [h_set, Finset.card_univ, Fintype.card_fin]

theorem thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter (n k c : ℕ) (hc : c ≤ n) (val : ℝ) :
    (Finset.filter (fun (i : Fin n) => (i : ℕ) < k) Finset.univ).sum
      (fun i => if (i : ℕ) < c then val else 0) = ((min k c : ℕ) : ℝ) * val := by
  have h_eq : (Finset.filter (fun (i : Fin n) => (i : ℕ) < k) Finset.univ).sum
      (fun i => if (i : ℕ) < c then val else 0) =
      ∑ i : Fin n, (if (i : ℕ) < min k c then val else 0) := by
    rw [Finset.sum_filter]
    have : ∀ i : Fin n, (if (i : ℕ) < k then if (i : ℕ) < c then val else 0 else 0) =
        (if (i : ℕ) < min k c then val else 0) := by
      intro i
      by_cases h1 : (i : ℕ) < k <;> by_cases h2 : (i : ℕ) < c <;> simp [h1, h2]
    simp_rw [this]
  rw [h_eq]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  have h_card := thermomajorization_pointwise_missed_error_ge_gap_error_card_fin_filter_lt n (min k c) ((min_le_right k c).trans hc)
  rw [h_card]

theorem thermomajorization_pointwise_missed_error_ge_gap_error_antitone_indicator (n c : ℕ) (val : ℝ) (hval : 0 ≤ val) :
    Antitone (fun (i : Fin n) => if (i : ℕ) < c then val else 0) := by
  intro i₁ i₂ hle
  by_cases h2 : (i₂ : ℕ) < c
  · have h1 : (i₁ : ℕ) < c := lt_of_le_of_lt hle h2
    simp [h1, h2]
  · simp [h2]
    split_ifs
    · exact hval
    · rfl

theorem thermomajorization_pointwise_missed_error_ge_gap_error_diff_sub_probe_le_one (n : ℕ) (F : Finset ℕ) (j : ℕ)
    (x y : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (hy : y ∈ stdSimplex ℝ (Fin n)) :
    thermomajorization_diff x y j - thermomajorization_probe_error n F x y ≤ 1 := by
  have h_diff : thermomajorization_diff x y j ≤ 1 := by
    unfold thermomajorization_diff
    have h1 : (Finset.filter (fun (i : Fin n) => (i.val < j)) Finset.univ).sum (fun i => y i - x i) ≤
              (Finset.filter (fun (i : Fin n) => (i.val < j)) Finset.univ).sum (fun i => y i) := by
      apply Finset.sum_le_sum
      intro i _
      have : 0 ≤ x i := hx.1 i
      linarith
    have h2 : (Finset.filter (fun (i : Fin n) => (i.val < j)) Finset.univ).sum (fun i => y i) ≤
              Finset.univ.sum (fun i => y i) := by
      apply Finset.sum_le_univ_sum_of_nonneg
      intro i
      exact hy.1 i
    have h3 : Finset.univ.sum (fun i => y i) = 1 := hy.2
    linarith
  have h_probe : 0 ≤ thermomajorization_probe_error n F x y := by
    dsimp [thermomajorization_probe_error]
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  linarith

theorem thermomajorization_pointwise_missed_error_ge_gap_error_le_iSup_2 {α β : Type*} (f : α → β → ℝ) (S : Set α) (T : Set β)
    (M : ℝ) (hM0 : 0 ≤ M) (hM : ∀ a ∈ S, ∀ b ∈ T, f a b ≤ M)
    {x : α} (hx : x ∈ S) {y : β} (hy : y ∈ T) :
    f x y ≤ ⨆ a ∈ S, ⨆ b ∈ T, f a b := by
  have h4 : f x y ≤ ⨆ (_ : y ∈ T), f x y := by
    have hbdd : BddAbove (Set.range (fun (_ : y ∈ T) => f x y)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨hy', rfl⟩
      exact hM x hx y hy'
    exact le_ciSup hbdd hy
  have h3 : (⨆ (_ : y ∈ T), f x y) ≤ ⨆ b, ⨆ (_ : b ∈ T), f x b := by
    have hbdd : BddAbove (Set.range (fun b => ⨆ (_ : b ∈ T), f x b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨b, rfl⟩
      refine Real.iSup_le (fun hb => hM x hx b hb) hM0
    exact le_ciSup hbdd y
  have h2 : (⨆ b, ⨆ (_ : b ∈ T), f x b) ≤ ⨆ (_ : x ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f x b := by
    have hbdd : BddAbove (Set.range (fun (_ : x ∈ S) => ⨆ b, ⨆ (_ : b ∈ T), f x b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨hx', rfl⟩
      refine Real.iSup_le (fun b => ?_) hM0
      refine Real.iSup_le (fun hb => hM x hx b hb) hM0
    exact le_ciSup hbdd hx
  have h1 : (⨆ (_ : x ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f x b) ≤
      ⨆ a, ⨆ (_ : a ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f a b := by
    have hbdd : BddAbove (Set.range (fun a => ⨆ (_ : a ∈ S), ⨆ b, ⨆ (_ : b ∈ T), f a b)) := by
      refine ⟨M, ?_⟩
      rintro z ⟨a, rfl⟩
      refine Real.iSup_le (fun ha => ?_) hM0
      refine Real.iSup_le (fun b => ?_) hM0
      refine Real.iSup_le (fun hb => hM a ha b hb) hM0
    exact le_ciSup hbdd x
  exact h4.trans (h3.trans (h2.trans h1))

/-- Lower bound on the pointwise thermomajorization missed error by the adjacent probe gap error. -/
theorem thermomajorization_pointwise_missed_error_ge_gap_error
    (n : ℕ) (hn : 2 ≤ n) (F : Finset ℕ) (hF : F ⊆ Finset.Ioo 0 n)
    (j : ℕ) (hj : j ∈ Finset.Ioo 0 n \ F) :
    let a := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
    let b := (insert n (F.filter (j < ·))).min' (Finset.insert_nonempty n _)
    thermomajorization_probe_gap_error a b j ≤
      thermomajorization_pointwise_missed_error n F j := by
  intro a b
  have hj_ioo : j ∈ Finset.Ioo 0 n := Finset.mem_sdiff.mp hj |>.1
  have hj_not_F : j ∉ F := Finset.mem_sdiff.mp hj |>.2
  rw [Finset.mem_Ioo] at hj_ioo
  obtain ⟨hj0, hjn⟩ := hj_ioo
  have ha_lt_j : a < j := by
    dsimp [a]
    have : ∀ x ∈ insert 0 (F.filter (· < j)), x < j := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter] at hx
      rcases hx with rfl | ⟨hx1, hx2⟩
      · exact hj0
      · exact hx2
    exact this a (Finset.max'_mem _ _)
  have hj_lt_b : j < b := by
    dsimp [b]
    have : ∀ x ∈ insert n (F.filter (j < ·)), j < x := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_filter] at hx
      rcases hx with rfl | ⟨hx1, hx2⟩
      · exact hjn
      · exact hx2
    exact this b (Finset.min'_mem _ _)
  have hb_le_n : b ≤ n := by
    dsimp [b]
    have hn_mem : n ∈ insert n (F.filter (j < ·)) := Finset.mem_insert_self _ _
    exact Finset.min'_le _ n hn_mem
  have ha_lt_b : a < b := ha_lt_j.trans hj_lt_b
  have ha_le_n : a ≤ n := (ha_lt_b.trans_le hb_le_n).le
  have hj_le_n : j ≤ n := hjn.le

  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr hj0
  have hba_pos : (0 : ℝ) < ((b : ℝ) - (a : ℝ)) := by
    rw [sub_pos]; exact Nat.cast_lt.mpr ha_lt_b
  have hdenom_pos : 0 < (j : ℝ) * ((b : ℝ) - (a : ℝ)) := mul_pos hj_pos hba_pos
  have hdenom_ne : (j : ℝ) * ((b : ℝ) - (a : ℝ)) ≠ 0 := hdenom_pos.ne'

  let d₁ : ℝ := ((b : ℝ) - (j : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))
  let d₂ : ℝ := ((j : ℝ) - (a : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))
  have hd₁_nonneg : 0 ≤ d₁ := by
    dsimp [d₁]
    apply div_nonneg
    · rw [sub_nonneg]; exact Nat.cast_le.mpr hj_lt_b.le
    · exact hdenom_pos.le
  have hd₂_nonneg : 0 ≤ d₂ := by
    dsimp [d₂]
    apply div_nonneg
    · rw [sub_nonneg]; exact Nat.cast_le.mpr ha_lt_j.le
    · exact hdenom_pos.le

  have hd_sum : d₁ + d₂ = 1 / (j : ℝ) := by
    dsimp [d₁, d₂]
    rw [← add_div]
    have h_num : ((b : ℝ) - (j : ℝ)) + ((j : ℝ) - (a : ℝ)) = (b : ℝ) - (a : ℝ) := by ring
    rw [h_num]
    have h_cancel : ((b : ℝ) - (a : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ))) =
        (1 : ℝ) / (j : ℝ) := by
      rw [mul_comm (j : ℝ)]
      have hx : ((b : ℝ) - (a : ℝ)) = ((b : ℝ) - (a : ℝ)) * 1 := (mul_one _).symm
      nth_rw 1 [hx]
      exact mul_div_mul_left 1 (j : ℝ) hba_pos.ne'
    exact h_cancel

  let x : Fin n → ℝ := fun i => (if (i : ℕ) < a then d₁ else 0) + (if (i : ℕ) < b then d₂ else 0)
  let y : Fin n → ℝ := fun i => if (i : ℕ) < j then d₁ + d₂ else 0

  have hx_nonneg : ∀ i, 0 ≤ x i := by
    intro i
    dsimp [x]
    apply add_nonneg <;> split_ifs <;> linarith
  have hy_nonneg : ∀ i, 0 ≤ y i := by
    intro i
    dsimp [y]
    split_ifs
    · linarith
    · rfl

  have hx_sum : ∑ i : Fin n, x i = 1 := by
    dsimp [x]
    rw [Finset.sum_add_distrib]
    have h_sum_a : ∑ i : Fin n, (if (i : ℕ) < a then d₁ else 0) = (a : ℝ) * d₁ := by
      have := thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n n a ha_le_n d₁
      have h_univ : (Finset.filter (fun (i : Fin n) => (i : ℕ) < n) Finset.univ) = Finset.univ := by
        ext ⟨i, hi⟩; simp
      rw [h_univ] at this
      rw [min_eq_right ha_le_n] at this
      exact this
    have h_sum_b : ∑ i : Fin n, (if (i : ℕ) < b then d₂ else 0) = (b : ℝ) * d₂ := by
      have := thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n n b hb_le_n d₂
      have h_univ : (Finset.filter (fun (i : Fin n) => (i : ℕ) < n) Finset.univ) = Finset.univ := by
        ext ⟨i, hi⟩; simp
      rw [h_univ] at this
      rw [min_eq_right hb_le_n] at this
      exact this
    rw [h_sum_a, h_sum_b]
    dsimp [d₁, d₂]
    have : (a : ℝ) * (((b : ℝ) - (j : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))) +
           (b : ℝ) * (((j : ℝ) - (a : ℝ)) / ((j : ℝ) * ((b : ℝ) - (a : ℝ)))) =
           ((a : ℝ) * ((b : ℝ) - (j : ℝ)) + (b : ℝ) * ((j : ℝ) - (a : ℝ))) / ((j : ℝ) * ((b : ℝ) - (a : ℝ))) := by
      ring
    rw [this]
    have h_alg : (a : ℝ) * ((b : ℝ) - (j : ℝ)) + (b : ℝ) * ((j : ℝ) - (a : ℝ)) =
                 (j : ℝ) * ((b : ℝ) - (a : ℝ)) := by ring
    rw [h_alg]
    exact div_self hdenom_ne

  have hy_sum : ∑ i : Fin n, y i = 1 := by
    dsimp [y]
    have := thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n n j hj_le_n (d₁ + d₂)
    have h_univ : (Finset.filter (fun (i : Fin n) => (i : ℕ) < n) Finset.univ) = Finset.univ := by
      ext ⟨i, hi⟩; simp
    rw [h_univ] at this
    rw [min_eq_right hj_le_n] at this
    rw [this, hd_sum, mul_one_div_cancel hj_pos.ne']

  have hx_anti : Antitone x := by
    dsimp [x]
    have h1 := thermomajorization_pointwise_missed_error_ge_gap_error_antitone_indicator n a d₁ hd₁_nonneg
    have h2 := thermomajorization_pointwise_missed_error_ge_gap_error_antitone_indicator n b d₂ hd₂_nonneg
    exact fun i₁ i₂ hle => add_le_add (h1 hle) (h2 hle)

  have hy_anti : Antitone y := by
    dsimp [y]
    have hd_sum_nonneg : 0 ≤ d₁ + d₂ := add_nonneg hd₁_nonneg hd₂_nonneg
    exact thermomajorization_pointwise_missed_error_ge_gap_error_antitone_indicator n j (d₁ + d₂) hd_sum_nonneg

  have hx_mem : x ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} :=
    ⟨⟨hx_nonneg, hx_sum⟩, hx_anti⟩
  have hy_mem : y ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} :=
    ⟨⟨hy_nonneg, hy_sum⟩, hy_anti⟩

  have h_diff_k : ∀ k, thermomajorization_diff x y k =
      ((min k j : ℕ) : ℝ) * (d₁ + d₂) - (((min k a : ℕ) : ℝ) * d₁ + ((min k b : ℕ) : ℝ) * d₂) := by
    intro k
    unfold thermomajorization_diff
    dsimp [x, y]
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    rw [thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n k j hj_le_n (d₁ + d₂)]
    rw [thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n k a ha_le_n d₁]
    rw [thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n k b hb_le_n d₂]

  have h_diff_F : ∀ k ∈ F, thermomajorization_diff x y k = 0 := by
    intro k hk
    have hkj : k ≠ j := by rintro rfl; exact hj_not_F hk
    rcases lt_or_gt_of_ne hkj with h_lt | h_gt
    · have hka : k ≤ a := by
        dsimp [a]
        have hk_mem : k ∈ insert 0 (F.filter (· < j)) := by simp [hk, h_lt]
        exact Finset.le_max' _ k hk_mem
      rw [h_diff_k k]
      have h1 : min k j = k := min_eq_left (hka.trans ha_lt_j.le)
      have h2 : min k a = k := min_eq_left hka
      have h3 : min k b = k := min_eq_left (hka.trans ha_lt_b.le)
      rw [h1, h2, h3]
      ring
    · have hbk : b ≤ k := by
        dsimp [b]
        have hk_mem : k ∈ insert n (F.filter (j < ·)) := by simp [hk, h_gt]
        exact Finset.min'_le _ k hk_mem
      rw [h_diff_k k]
      have h1 : min k j = j := min_eq_right (hj_lt_b.le.trans hbk)
      have h2 : min k a = a := min_eq_right (ha_lt_b.le.trans hbk)
      have h3 : min k b = b := min_eq_right hbk
      rw [h1, h2, h3]
      dsimp [d₁, d₂]
      ring

  have h_probe_zero : thermomajorization_probe_error n F x y = 0 := by
    dsimp [thermomajorization_probe_error]
    apply le_antisymm
    · rw [Finset.max'_le_iff]
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_image] at hz
      rcases hz with rfl | ⟨k, hk, rfl⟩
      · rfl
      · rw [h_diff_F k hk]
    · exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)

  have h_diff_j : thermomajorization_diff x y j = thermomajorization_probe_gap_error a b j := by
    rw [h_diff_k j]
    have h1 : min j j = j := min_self j
    have h2 : min j a = a := min_eq_right ha_lt_j.le
    have h3 : min j b = j := min_eq_left hj_lt_b.le
    rw [h1, h2, h3]
    dsimp [d₁, d₂, thermomajorization_probe_gap_error]
    ring

  have h_target : thermomajorization_probe_gap_error a b j =
      thermomajorization_diff x y j - thermomajorization_probe_error n F x y := by
    rw [h_diff_j, h_probe_zero, sub_zero]

  rw [h_target]
  have hM : ∀ x' ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v},
            ∀ y' ∈ {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v},
            thermomajorization_diff x' y' j - thermomajorization_probe_error n F x' y' ≤ 1 := by
    intro x' hx' y' hy'
    exact thermomajorization_pointwise_missed_error_ge_gap_error_diff_sub_probe_le_one n F j x' y' hx'.1 hy'.1
  exact thermomajorization_pointwise_missed_error_ge_gap_error_le_iSup_2 (fun x' y' => thermomajorization_diff x' y' j - thermomajorization_probe_error n F x' y')
    {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v} {v | v ∈ stdSimplex ℝ (Fin n) ∧ Antitone v}
    1 zero_le_one hM hx_mem hy_mem
