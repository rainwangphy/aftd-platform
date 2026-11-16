import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedError
import AFTD.Kb.Physics.ThermomajorizationProbeGapError
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedErrorGeGapError
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.ThermomajorizationDiffZero
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# thermomajorization_pointwise_missed_error_le_gap_error

Topic: quantum_mechanics   Node: fb5a87924b74

Provenance: helper lemma. arXiv:2610.35433, Population capacity and the geometry of thermomajorization

For any dimension n ≥ 2, probe set F ⊆ {1,...,n-1}, and unprobed rank j ∈ {1,...,n-1} \ F, the pointwise missed error thermomajorization_pointwise_missed_error n F j is bounded above by thermomajorization_probe_gap_error a b j, where a = max({0} ∪ {k ∈ F : k < j}) and b = min({n} ∪ {k ∈ F : k > j}).
-/

open Finset

def thermomajorization_pointwise_missed_error_le_gap_error_pref (n : ℕ) (k : ℕ) : Finset (Fin n) :=
  Finset.filter (fun (i : Fin n) => (i : ℕ) < k) Finset.univ

def thermomajorization_pointwise_missed_error_le_gap_error_interval (n : ℕ) (a b : ℕ) : Finset (Fin n) :=
  Finset.filter (fun (i : Fin n) => a ≤ (i : ℕ) ∧ (i : ℕ) < b) Finset.univ

lemma thermomajorization_pointwise_missed_error_le_gap_error_card_pref (n k : ℕ) (hk : k ≤ n) :
    (thermomajorization_pointwise_missed_error_le_gap_error_pref n k).card = k := by
  have h := thermomajorization_pointwise_missed_error_ge_gap_error_sum_indicator_filter n k k hk 1
  rw [min_self, mul_one] at h
  have h_congr : ∀ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n k,
      (if (i : ℕ) < k then (1 : ℝ) else 0) = 1 := by
    intro i hi; rw [thermomajorization_pointwise_missed_error_le_gap_error_pref, mem_filter] at hi; exact if_pos hi.2
  change (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n k,
    if (i : ℕ) < k then (1 : ℝ) else 0) = (k : ℝ) at h
  rw [sum_congr rfl h_congr, sum_const, nsmul_eq_mul, mul_one] at h
  exact Nat.cast_injective h

lemma thermomajorization_pointwise_missed_error_le_gap_error_card_interval (n : ℕ) {a b : ℕ}
    (hab : a ≤ b) (hbn : b ≤ n) :
    (thermomajorization_pointwise_missed_error_le_gap_error_interval n a b).card = b - a := by
  have h_disj : Disjoint (thermomajorization_pointwise_missed_error_le_gap_error_pref n a)
      (thermomajorization_pointwise_missed_error_le_gap_error_interval n a b) := by
    dsimp [thermomajorization_pointwise_missed_error_le_gap_error_pref,
      thermomajorization_pointwise_missed_error_le_gap_error_interval]
    rw [disjoint_filter]; intro x _ hx1 ⟨hx2, _⟩; omega
  have h_union : thermomajorization_pointwise_missed_error_le_gap_error_pref n a ∪
      thermomajorization_pointwise_missed_error_le_gap_error_interval n a b =
      thermomajorization_pointwise_missed_error_le_gap_error_pref n b := by
    ext ⟨i, hi⟩
    simp only [thermomajorization_pointwise_missed_error_le_gap_error_pref,
      thermomajorization_pointwise_missed_error_le_gap_error_interval, mem_union, mem_filter, mem_univ, true_and]
    omega
  have h_card := card_union_of_disjoint h_disj
  rw [h_union, thermomajorization_pointwise_missed_error_le_gap_error_card_pref n a (hab.trans hbn),
      thermomajorization_pointwise_missed_error_le_gap_error_card_pref n b hbn] at h_card
  omega

lemma thermomajorization_pointwise_missed_error_le_gap_error_diff_a_le_probe {n : ℕ} (F : Finset ℕ) (j : ℕ)
    (x y : Fin n → ℝ) :
    let a := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
    thermomajorization_diff x y a ≤ thermomajorization_probe_error n F x y := by
  intro a
  have ha_mem : a ∈ insert 0 (F.filter (· < j)) := Finset.max'_mem _ _
  simp only [Finset.mem_insert, Finset.mem_filter] at ha_mem
  rcases ha_mem with ha0 | ⟨ha_F, _⟩
  · rw [ha0, thermomajorization_diff_zero]
    dsimp [thermomajorization_probe_error]
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  · dsimp [thermomajorization_probe_error]
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ ha_F)

lemma thermomajorization_pointwise_missed_error_le_gap_error_diff_b_le_probe {n : ℕ} (F : Finset ℕ) (j : ℕ)
    (x y : Fin n → ℝ) (hx : x ∈ stdSimplex ℝ (Fin n)) (hy : y ∈ stdSimplex ℝ (Fin n)) :
    let b := (insert n (F.filter (j < ·))).min' (Finset.insert_nonempty n _)
    thermomajorization_diff x y b ≤ thermomajorization_probe_error n F x y := by
  intro b
  have hb_mem : b ∈ insert n (F.filter (j < ·)) := Finset.min'_mem _ _
  simp only [Finset.mem_insert, Finset.mem_filter] at hb_mem
  rcases hb_mem with hbn | ⟨hb_F, _⟩
  · have h0 : thermomajorization_diff x y n = 0 := by
      unfold thermomajorization_diff
      have h_univ : (Finset.filter (fun (i : Fin n) => (i : ℕ) < n) Finset.univ) = Finset.univ := by
        ext ⟨i, _⟩; simp
      rw [h_univ, Finset.sum_sub_distrib, hy.2, hx.2, sub_self]
    rw [hbn, h0]
    dsimp [thermomajorization_probe_error]
    exact Finset.le_max' _ 0 (Finset.mem_insert_self 0 _)
  · dsimp [thermomajorization_probe_error]
    apply Finset.le_max'
    exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hb_F)

lemma thermomajorization_pointwise_missed_error_le_gap_error_sum_decomp {n : ℕ} (f : Fin n → ℝ) {a b : ℕ} (hab : a ≤ b) :
    (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n b, f i) =
      (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a, f i) +
      (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a b, f i) := by
  have h_disj : Disjoint (thermomajorization_pointwise_missed_error_le_gap_error_pref n a)
      (thermomajorization_pointwise_missed_error_le_gap_error_interval n a b) := by
    dsimp [thermomajorization_pointwise_missed_error_le_gap_error_pref,
      thermomajorization_pointwise_missed_error_le_gap_error_interval]
    rw [disjoint_filter]; intro x _ hx1 ⟨hx2, _⟩; omega
  have h_union : thermomajorization_pointwise_missed_error_le_gap_error_pref n a ∪
      thermomajorization_pointwise_missed_error_le_gap_error_interval n a b =
      thermomajorization_pointwise_missed_error_le_gap_error_pref n b := by
    ext ⟨i, hi⟩
    simp only [thermomajorization_pointwise_missed_error_le_gap_error_pref,
      thermomajorization_pointwise_missed_error_le_gap_error_interval, mem_union, mem_filter, mem_univ, true_and]
    omega
  rw [← sum_union h_disj, h_union]

lemma thermomajorization_pointwise_missed_error_le_gap_error_sum_y_interval_le (n a j : ℕ) (ha : a < j) (hjn : j ≤ n)
    (y : Fin n → ℝ) (hy : y ∈ stdSimplex ℝ (Fin n)) (hy_anti : Antitone y) :
    ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i ≤ (j - a : ℝ) / (j : ℝ) := by
  have hj_pos : (0 : ℝ) < (j : ℝ) := Nat.cast_pos.mpr (Nat.lt_of_le_of_lt (Nat.zero_le a) ha)
  have h_inner : ∀ i₀ ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a,
      ∑ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, (y i₀ - y i₁) =
        (j - a : ℝ) * y i₀ - ∑ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i₁ := by
    intro i₀ _
    rw [sum_sub_distrib, sum_const, thermomajorization_pointwise_missed_error_le_gap_error_card_interval n ha.le hjn,
        nsmul_eq_mul, Nat.cast_sub ha.le]
  have h_double : ∑ i₀ ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a,
      ∑ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, (y i₀ - y i₁) =
      (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a, y i) -
      (a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) := by
    rw [sum_congr rfl h_inner, sum_sub_distrib, ← mul_sum, sum_const,
        thermomajorization_pointwise_missed_error_le_gap_error_card_pref n a (ha.le.trans hjn), nsmul_eq_mul]
  have h_nonneg : 0 ≤ ∑ i₀ ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a,
      ∑ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, (y i₀ - y i₁) := by
    apply sum_nonneg; intro i₀ hi₀
    apply sum_nonneg; intro i₁ hi₁
    rw [thermomajorization_pointwise_missed_error_le_gap_error_pref, mem_filter] at hi₀
    rw [thermomajorization_pointwise_missed_error_le_gap_error_interval, mem_filter] at hi₁
    have hle : i₀ ≤ i₁ := by rw [Fin.le_iff_val_le_val]; exact hi₀.2.le.trans hi₁.2.1
    have := hy_anti hle
    linarith
  rw [h_double] at h_nonneg
  have h_sum_union : (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a, y i) +
      (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) =
      ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, y i :=
    (thermomajorization_pointwise_missed_error_le_gap_error_sum_decomp y ha.le).symm
  have h_sum_le_one : ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, y i ≤ 1 := by
    have h_sub : thermomajorization_pointwise_missed_error_le_gap_error_pref n j ⊆ Finset.univ := subset_univ _
    have := sum_le_sum_of_subset_of_nonneg h_sub (fun i _ _ => hy.1 i)
    rw [hy.2] at this; exact this
  have h_comb : (j : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) ≤
      (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, y i) := by
    calc (j : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i)
      _ = (a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) +
          (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) := by ring
      _ ≤ (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a, y i) +
          (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) := by linarith
      _ = (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, y i) := by
        rw [← mul_add, h_sum_union]
  have h_sub_pos : 0 ≤ (j - a : ℝ) := by rw [sub_nonneg]; exact Nat.cast_le.mpr ha.le
  have h_top : (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i) * (j : ℝ) ≤
      (j - a : ℝ) := by
    rw [mul_comm]
    calc (j : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i)
      _ ≤ (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, y i) := h_comb
      _ ≤ (j - a : ℝ) * 1 := mul_le_mul_of_nonneg_left h_sum_le_one h_sub_pos
      _ = (j - a : ℝ) := mul_one _
  exact (le_div_iff₀ hj_pos).mpr h_top

lemma thermomajorization_pointwise_missed_error_le_gap_error_double_sum_x_nonneg (n a b j : ℕ)
    (ha : a ≤ j) (hb : j ≤ b) (hbn : b ≤ n) (x : Fin n → ℝ) (hx_anti : Antitone x) :
    0 ≤ (b - j : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, x i) -
        (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, x i) := by
  have h_inner : ∀ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j,
      ∑ i₂ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, (x i₁ - x i₂) =
        (b - j : ℝ) * x i₁ - ∑ i₂ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, x i₂ := by
    intro i₁ _
    rw [sum_sub_distrib, sum_const,
        thermomajorization_pointwise_missed_error_le_gap_error_card_interval n hb hbn,
        nsmul_eq_mul, Nat.cast_sub hb]
  have h_double : ∑ i₁ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j,
      ∑ i₂ ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, (x i₁ - x i₂) =
      (b - j : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, x i) -
      (j - a : ℝ) * (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, x i) := by
    rw [sum_congr rfl h_inner, sum_sub_distrib, ← mul_sum, sum_const,
        thermomajorization_pointwise_missed_error_le_gap_error_card_interval n ha (hb.trans hbn),
        nsmul_eq_mul, Nat.cast_sub ha]
  rw [← h_double]
  apply sum_nonneg; intro i₁ hi₁
  apply sum_nonneg; intro i₂ hi₂
  rw [thermomajorization_pointwise_missed_error_le_gap_error_interval, mem_filter] at hi₁ hi₂
  have hle : i₁ ≤ i₂ := by rw [Fin.le_iff_val_le_val]; exact hi₁.2.2.le.trans hi₂.2.1
  have := hx_anti hle
  linarith

/-- Upper bound on the pointwise thermomajorization missed error by the adjacent probe gap error. -/
theorem thermomajorization_pointwise_missed_error_le_gap_error
    (n : ℕ) (hn : 2 ≤ n) (F : Finset ℕ) (hF : F ⊆ Finset.Ioo 0 n)
    (j : ℕ) (hj : j ∈ Finset.Ioo 0 n \ F) :
    let a := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
    let b := (insert n (F.filter (j < ·))).min' (Finset.insert_nonempty n _)
    thermomajorization_pointwise_missed_error n F j ≤
      thermomajorization_probe_gap_error a b j := by
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
  have hba_ne : (b : ℝ) - (a : ℝ) ≠ 0 := hba_pos.ne'
  have hdenom_pos : 0 < (j : ℝ) * ((b : ℝ) - (a : ℝ)) := mul_pos hj_pos hba_pos
  have h_gap_nonneg : 0 ≤ thermomajorization_probe_gap_error a b j := by
    dsimp [thermomajorization_probe_gap_error]
    apply div_nonneg
    · apply mul_nonneg
      · rw [sub_nonneg]; exact Nat.cast_le.mpr ha_lt_j.le
      · rw [sub_nonneg]; exact Nat.cast_le.mpr hj_lt_b.le
    · exact hdenom_pos.le

  let p : ℝ := ((b : ℝ) - (j : ℝ)) / ((b : ℝ) - (a : ℝ))
  let q : ℝ := ((j : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ))
  have hp_nonneg : 0 ≤ p := by
    dsimp [p]; apply div_nonneg
    · rw [sub_nonneg]; exact Nat.cast_le.mpr hj_lt_b.le
    · exact hba_pos.le
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]; apply div_nonneg
    · rw [sub_nonneg]; exact Nat.cast_le.mpr ha_lt_j.le
    · exact hba_pos.le
  have hpq : p + q = 1 := by
    dsimp [p, q]; rw [← add_div]
    have : ((b : ℝ) - (j : ℝ)) + ((j : ℝ) - (a : ℝ)) = (b : ℝ) - (a : ℝ) := by ring
    rw [this, div_self hba_ne]

  dsimp [thermomajorization_pointwise_missed_error]
  refine Real.iSup_le (fun x => ?_) h_gap_nonneg
  refine Real.iSup_le (fun hx => ?_) h_gap_nonneg
  refine Real.iSup_le (fun y => ?_) h_gap_nonneg
  refine Real.iSup_le (fun hy => ?_) h_gap_nonneg

  have hx_anti : Antitone x := hx.2
  have hy_anti : Antitone y := hy.2
  have hx_std : x ∈ stdSimplex ℝ (Fin n) := hx.1
  have hy_std : y ∈ stdSimplex ℝ (Fin n) := hy.1

  have hDa : thermomajorization_diff x y a ≤ thermomajorization_probe_error n F x y :=
    thermomajorization_pointwise_missed_error_le_gap_error_diff_a_le_probe F j x y
  have hDb : thermomajorization_diff x y b ≤ thermomajorization_probe_error n F x y :=
    thermomajorization_pointwise_missed_error_le_gap_error_diff_b_le_probe F j x y hx_std hy_std

  have hE_bound : p * thermomajorization_diff x y a + q * thermomajorization_diff x y b ≤
      thermomajorization_probe_error n F x y := by
    calc p * thermomajorization_diff x y a + q * thermomajorization_diff x y b
      _ ≤ p * thermomajorization_probe_error n F x y + q * thermomajorization_probe_error n F x y :=
        add_le_add (mul_le_mul_of_nonneg_left hDa hp_nonneg) (mul_le_mul_of_nonneg_left hDb hq_nonneg)
      _ = (p + q) * thermomajorization_probe_error n F x y := by ring
      _ = thermomajorization_probe_error n F x y := by rw [hpq, one_mul]

  have h_diff_bound : thermomajorization_diff x y j - thermomajorization_probe_error n F x y ≤
      thermomajorization_diff x y j - (p * thermomajorization_diff x y a + q * thermomajorization_diff x y b) := by
    linarith

  let Sa := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n a, (y i - x i)
  let S1 := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, (y i - x i)
  let S2 := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, (y i - x i)

  have hdj : thermomajorization_diff x y j = Sa + S1 := by
    change (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n j, (y i - x i)) = Sa + S1
    exact thermomajorization_pointwise_missed_error_le_gap_error_sum_decomp (fun i => y i - x i) ha_lt_j.le
  have hda : thermomajorization_diff x y a = Sa := rfl
  have hdb : thermomajorization_diff x y b = Sa + S1 + S2 := by
    change (∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_pref n b, (y i - x i)) = Sa + S1 + S2
    have h1 := thermomajorization_pointwise_missed_error_le_gap_error_sum_decomp (fun i => y i - x i) ha_lt_j.le
    have h2 := thermomajorization_pointwise_missed_error_le_gap_error_sum_decomp (fun i => y i - x i) hj_lt_b.le
    rw [h2, h1, add_assoc]

  have h_alg : thermomajorization_diff x y j - (p * thermomajorization_diff x y a + q * thermomajorization_diff x y b) =
      p * S1 - q * S2 := by
    rw [hdj, hda, hdb]
    calc (Sa + S1) - (p * Sa + q * (Sa + S1 + S2))
      _ = (1 - p - q) * Sa + (1 - q) * S1 - q * S2 := by ring
      _ = 0 * Sa + p * S1 - q * S2 := by
        have h1 : 1 - p - q = 0 := by linarith
        have h2 : 1 - q = p := by linarith
        rw [h1, h2]
      _ = p * S1 - q * S2 := by ring

  let S1y := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, y i
  let S1x := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n a j, x i
  let S2y := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, y i
  let S2x := ∑ i ∈ thermomajorization_pointwise_missed_error_le_gap_error_interval n j b, x i

  have hS1 : S1 = S1y - S1x := by dsimp [S1, S1y, S1x]; rw [sum_sub_distrib]
  have hS2 : S2 = S2y - S2x := by dsimp [S2, S2y, S2x]; rw [sum_sub_distrib]

  have h_split : p * S1 - q * S2 = (p * S1y - q * S2y) - (p * S1x - q * S2x) := by
    rw [hS1, hS2]; ring

  have h_x_nonneg : 0 ≤ p * S1x - q * S2x := by
    have h_double := thermomajorization_pointwise_missed_error_le_gap_error_double_sum_x_nonneg n a b j
      ha_lt_j.le hj_lt_b.le hb_le_n x hx_anti
    dsimp [p, q]
    have : ((b : ℝ) - (j : ℝ)) / ((b : ℝ) - (a : ℝ)) * S1x - ((j : ℝ) - (a : ℝ)) / ((b : ℝ) - (a : ℝ)) * S2x =
        (((b : ℝ) - (j : ℝ)) * S1x - ((j : ℝ) - (a : ℝ)) * S2x) / ((b : ℝ) - (a : ℝ)) := by ring
    rw [this]
    exact div_nonneg h_double hba_pos.le

  have h_y_le : S1y ≤ (j - a : ℝ) / (j : ℝ) :=
    thermomajorization_pointwise_missed_error_le_gap_error_sum_y_interval_le n a j ha_lt_j hj_le_n y hy_std hy_anti

  have h_S2y_nonneg : 0 ≤ S2y := sum_nonneg (fun i _ => hy_std.1 i)

  have h_main : p * S1 - q * S2 ≤ thermomajorization_probe_gap_error a b j := by
    rw [h_split]
    calc (p * S1y - q * S2y) - (p * S1x - q * S2x)
      _ ≤ p * S1y - q * S2y := by linarith
      _ ≤ p * S1y := by
        have : 0 ≤ q * S2y := mul_nonneg hq_nonneg h_S2y_nonneg
        linarith
      _ ≤ p * (((j - a : ℝ)) / (j : ℝ)) := mul_le_mul_of_nonneg_left h_y_le hp_nonneg
      _ = thermomajorization_probe_gap_error a b j := by
        dsimp [p, thermomajorization_probe_gap_error]
        rw [div_mul_div_comm, mul_comm ((b : ℝ) - (j : ℝ)), mul_comm ((b : ℝ) - (a : ℝ))]

  linarith
