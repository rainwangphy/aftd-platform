import AFTD.Prelude
import AFTD.Kb.Tcs.PrefixReversal

/-!
# prefix_reversal_gcd_diff_necessary

Topic: combinatorics   Node: a424c1b769a5

Provenance: formalization of a published result. Source: arXiv:2610.30892 Lemma 3.2

If three prefix reversals of lengths k, m, n with 2 ≤ k < m < n generate the symmetric group Equiv.Perm (Fin n), then gcd(n - m, n - k) = 1.
-/

lemma prefix_reversal_gcd_diff_necessary_apply_of_lt (n k : ℕ) (j : Fin n)
    (h : j.val < k) (hk : k ≤ n) :
    (prefixReversal n k j).val = k - 1 - j.val := by
  simp [prefixReversal, h, hk]

lemma prefix_reversal_gcd_diff_necessary_apply_of_ge (n k : ℕ) (j : Fin n)
    (h : k ≤ j.val) :
    prefixReversal n k j = j := by
  have hlt : ¬ j.val < k := by omega
  simp [prefixReversal, hlt]

lemma prefix_reversal_gcd_diff_necessary_cast_pred_eq (d n i : ℕ)
    (hi : i ≤ n) (hi1 : 1 ≤ i) (hn1 : 1 ≤ n) (hdiv : d ∣ n - i) :
    ((i - 1 : ℕ) : ZMod d) = ((n - 1 : ℕ) : ZMod d) := by
  have hcast : (i : ZMod d) = (n : ZMod d) := by
    rw [ZMod.natCast_eq_natCast_iff]
    exact (Nat.modEq_iff_dvd' hi).mpr hdiv
  have hi_sub : ((i - 1 : ℕ) : ZMod d) = (i : ZMod d) - 1 := by
    rw [Nat.cast_sub hi1]; norm_num
  have hn_sub : ((n - 1 : ℕ) : ZMod d) = (n : ZMod d) - 1 := by
    rw [Nat.cast_sub hn1]; norm_num
  rw [hi_sub, hn_sub, hcast]

lemma prefix_reversal_gcd_diff_necessary_zmod_pair_reverse {d : ℕ}
    (t x : ZMod d) :
    (x = 0 ∨ x = t) ↔ (t - x = 0 ∨ t - x = t) := by
  constructor
  · rintro (h | h)
    · right; rw [h]; simp
    · left; rw [h]; simp
  · rintro (h | h)
    · right
      calc x = t - (t - x) := by abel
        _ = t - 0 := by rw [h]
        _ = t := by simp
    · left
      calc x = t - (t - x) := by abel
        _ = t - t := by rw [h]
        _ = 0 := by simp

lemma prefix_reversal_gcd_diff_necessary_set_preserved {d n i : ℕ}
    (hi1 : 1 ≤ i) (hi2 : i ≤ n) (hn1 : 1 ≤ n) (hdiv : d ∣ n - i) :
    ∀ x : Fin n,
      ((x.val : ZMod d) = 0 ∨ (x.val : ZMod d) = ((n - 1 : ℕ) : ZMod d)) ↔
      (((prefixReversal n i x).val : ZMod d) = 0 ∨
        ((prefixReversal n i x).val : ZMod d) = ((n - 1 : ℕ) : ZMod d)) := by
  intro x
  by_cases hx : x.val < i
  · have hcalc : (((prefixReversal n i x).val : ZMod d)) =
        ((n - 1 : ℕ) : ZMod d) - (x.val : ZMod d) := by
      rw [prefix_reversal_gcd_diff_necessary_apply_of_lt n i x hx hi2]
      have hxle : x.val ≤ i - 1 := by omega
      rw [Nat.cast_sub hxle]
      have hpred : ((i - 1 : ℕ) : ZMod d) = ((n - 1 : ℕ) : ZMod d) :=
        prefix_reversal_gcd_diff_necessary_cast_pred_eq d n i hi2 hi1 hn1 hdiv
      rw [hpred]
    rw [hcalc]
    exact prefix_reversal_gcd_diff_necessary_zmod_pair_reverse _ _
  · have hxge : i ≤ x.val := by omega
    rw [prefix_reversal_gcd_diff_necessary_apply_of_ge n i x hxge]

lemma prefix_reversal_gcd_diff_necessary_pair_preserved {n i : ℕ}
    (hi : i % 2 = 0) (hin : i ≤ n) :
    ∀ x y : Fin n, x.val / 2 = y.val / 2 ↔
      (prefixReversal n i x).val / 2 = (prefixReversal n i y).val / 2 := by
  intro x y
  by_cases hx : x.val < i
  · by_cases hy : y.val < i
    · rw [prefix_reversal_gcd_diff_necessary_apply_of_lt n i x hx hin,
        prefix_reversal_gcd_diff_necessary_apply_of_lt n i y hy hin]
      constructor <;> intro h <;> omega
    · have hyge : i ≤ y.val := by omega
      rw [prefix_reversal_gcd_diff_necessary_apply_of_lt n i x hx hin,
        prefix_reversal_gcd_diff_necessary_apply_of_ge n i y hyge]
      constructor <;> intro h <;> omega
  · have hxge : i ≤ x.val := by omega
    by_cases hy : y.val < i
    · rw [prefix_reversal_gcd_diff_necessary_apply_of_ge n i x hxge,
        prefix_reversal_gcd_diff_necessary_apply_of_lt n i y hy hin]
      constructor <;> intro h <;> omega
    · have hyge : i ≤ y.val := by omega
      rw [prefix_reversal_gcd_diff_necessary_apply_of_ge n i x hxge,
        prefix_reversal_gcd_diff_necessary_apply_of_ge n i y hyge]

lemma prefix_reversal_gcd_diff_necessary_parity_fiber {n i : ℕ}
    (hi : i % 2 = 1) (hin : i ≤ n) :
    ∀ x y : Fin n, x.val % 2 = y.val % 2 ↔
      (prefixReversal n i x).val % 2 = (prefixReversal n i y).val % 2 := by
  intro x y
  have key : ∀ z : Fin n, z.val % 2 = (prefixReversal n i z).val % 2 := by
    intro z
    by_cases hz : z.val < i
    · rw [prefix_reversal_gcd_diff_necessary_apply_of_lt n i z hz hin]; omega
    · have hzge : i ≤ z.val := by omega
      rw [prefix_reversal_gcd_diff_necessary_apply_of_ge n i z hzge]
  rw [key x, key y]

def prefix_reversal_gcd_diff_necessary_stabilizer_set {α : Type} (S : Set α) :
    Subgroup (Equiv.Perm α) where
  carrier := {σ | ∀ x, x ∈ S ↔ σ x ∈ S}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro σ τ hσ hτ x
    rw [Equiv.Perm.mul_apply]
    exact (hτ x).trans (hσ (τ x))
  inv_mem' := by
    intro σ hσ x
    have h := (hσ (σ⁻¹ x)).symm
    simpa using h

def prefix_reversal_gcd_diff_necessary_fiber_rel {n : ℕ} (q : Fin n → ℕ) :
    Subgroup (Equiv.Perm (Fin n)) where
  carrier := {σ | ∀ x y, q x = q y ↔ q (σ x) = q (σ y)}
  one_mem' := by intro x y; simp
  mul_mem' := by
    intro σ τ hσ hτ x y
    rw [Equiv.Perm.mul_apply]
    exact (hτ x y).trans (hσ (τ x) (τ y))
  inv_mem' := by
    intro σ hσ x y
    have h := (hσ (σ⁻¹ x) (σ⁻¹ y)).symm
    simpa using h

lemma prefix_reversal_gcd_diff_necessary_stabilizer_set_ne_top {n : ℕ}
    (S : Set (Fin n)) (a b : Fin n) (ha : a ∈ S) (hb : b ∉ S) :
    prefix_reversal_gcd_diff_necessary_stabilizer_set S ≠ ⊤ := by
  intro htop
  have hmem : Equiv.swap a b ∈ prefix_reversal_gcd_diff_necessary_stabilizer_set S := by
    rw [htop]; exact Subgroup.mem_top _
  have h := hmem a
  rw [Equiv.swap_apply_left] at h
  exact hb (h.mp ha)

lemma prefix_reversal_gcd_diff_necessary_fiber_ne_top {n : ℕ}
    (q : Fin n → ℕ) {a b c : Fin n} (hab : q a = q b) (hac : q a ≠ q c)
    (hba : b ≠ a) (hca : c ≠ a) :
    prefix_reversal_gcd_diff_necessary_fiber_rel q ≠ ⊤ := by
  intro htop
  have hmem : Equiv.swap b c ∈ prefix_reversal_gcd_diff_necessary_fiber_rel q := by
    rw [htop]; exact Subgroup.mem_top _
  have h := hmem a b
  rw [Equiv.swap_apply_of_ne_of_ne (a := b) (b := c) (x := a) (Ne.symm hba) (Ne.symm hca),
    Equiv.swap_apply_left] at h
  exact hac (h.mp hab)

lemma prefix_reversal_gcd_diff_necessary_zmod_one_ne_zero {d : ℕ} (hd : 1 < d) :
    (1 : ZMod d) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_zero] at hv
  have h1 : ZMod.val (1 : ZMod d) = 1 := by simpa using ZMod.val_cast_of_lt hd
  omega

lemma prefix_reversal_gcd_diff_necessary_zmod_two_ne_zero {d : ℕ} (hd : 2 < d) :
    (2 : ZMod d) ≠ 0 := by
  intro h
  have hv := congrArg ZMod.val h
  rw [ZMod.val_zero] at hv
  have h2 : ZMod.val (2 : ZMod d) = 2 := by simpa using ZMod.val_cast_of_lt hd
  omega

lemma prefix_reversal_gcd_diff_necessary_zmod_two_ne_one {d : ℕ} (hd : 2 < d) :
    (2 : ZMod d) ≠ 1 := by
  intro h
  have hv := congrArg ZMod.val h
  have h2 : ZMod.val (2 : ZMod d) = 2 := by simpa using ZMod.val_cast_of_lt hd
  have h1 : ZMod.val (1 : ZMod d) = 1 := by
    simpa using ZMod.val_cast_of_lt (by omega : 1 < d)
  omega

lemma prefix_reversal_gcd_diff_necessary_exists_zmod_not_pair {d : ℕ}
    (hd3 : 3 ≤ d) (t : ZMod d) : ∃ y : ZMod d, y ≠ 0 ∧ y ≠ t := by
  by_cases ht0 : t = 0
  · refine ⟨1, prefix_reversal_gcd_diff_necessary_zmod_one_ne_zero (by omega), ?_⟩
    intro h
    rw [ht0] at h
    exact prefix_reversal_gcd_diff_necessary_zmod_one_ne_zero (by omega) h
  · by_cases ht1 : t = 1
    · refine ⟨2, prefix_reversal_gcd_diff_necessary_zmod_two_ne_zero (by omega), ?_⟩
      intro h
      rw [ht1] at h
      exact prefix_reversal_gcd_diff_necessary_zmod_two_ne_one (by omega) h
    · refine ⟨1, prefix_reversal_gcd_diff_necessary_zmod_one_ne_zero (by omega), ?_⟩
      intro h
      exact ht1 h.symm

lemma prefix_reversal_gcd_diff_necessary_zmod_val_lt {d : ℕ} (hd : 0 < d)
    (y : ZMod d) : y.val < d := by
  haveI : NeZero d := ⟨by omega⟩
  exact ZMod.val_lt y

lemma prefix_reversal_gcd_diff_necessary_cast_val {d : ℕ} (hd : 0 < d)
    (y : ZMod d) : ((y.val : ℕ) : ZMod d) = y := by
  haveI : NeZero d := ⟨by omega⟩
  exact ZMod.natCast_zmod_val y

/-- Generation of the symmetric group by three prefix reversals requires gcd(n - m, n - k) = 1. -/
theorem prefix_reversal_gcd_diff_necessary (k m n : ℕ)
    (hk : 2 ≤ k) (hkm : k < m) (hmn : m < n)
    (hgen : Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} = ⊤) :
    Nat.gcd (n - m) (n - k) = 1 := by
  by_contra hne
  set d := Nat.gcd (n - m) (n - k) with hd
  have hn1 : 1 ≤ n := by omega
  have hkn : k ≤ n := by omega
  have hmn' : m ≤ n := by omega
  have hk1 : 1 ≤ k := by omega
  have hm1 : 1 ≤ m := by omega
  have hdivk : d ∣ n - k := hd ▸ Nat.gcd_dvd_right _ _
  have hdivm : d ∣ n - m := hd ▸ Nat.gcd_dvd_left _ _
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdivk (by omega)
  have hdn : d ≤ n := by
    have h1 : d ≤ n - k := Nat.le_of_dvd (by omega) hdivk
    omega
  rcases Nat.lt_or_ge d 3 with hd3 | hd3
  · have hd2' : d = 2 := by omega
    have hdivk2 : 2 ∣ n - k := hd2' ▸ hdivk
    have hdivm2 : 2 ∣ n - m := hd2' ▸ hdivm
    have hn4 : 4 ≤ n := by omega
    rcases Nat.mod_two_eq_zero_or_one n with hnpar | hnpar
    · have hk2 : k % 2 = 0 := by obtain ⟨c, hc⟩ := hdivk2; omega
      have hm2 : m % 2 = 0 := by obtain ⟨c, hc⟩ := hdivm2; omega
      set q : Fin n → ℕ := fun x => x.val / 2 with hq
      have hK : prefix_reversal_gcd_diff_necessary_fiber_rel q ≠ ⊤ := by
        refine prefix_reversal_gcd_diff_necessary_fiber_ne_top q
          (a := ⟨0, by omega⟩) (b := ⟨1, by omega⟩) (c := ⟨2, by omega⟩) ?_ ?_ ?_ ?_
        · show (0:ℕ)/2 = 1/2; rfl
        · show (0:ℕ)/2 ≠ 2/2; norm_num
        · show (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩; intro h; simp at h
        · show (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩; intro h; simp at h
      have hsub : Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} ≤
          prefix_reversal_gcd_diff_necessary_fiber_rel q := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact prefix_reversal_gcd_diff_necessary_pair_preserved hk2 hkn
        · exact prefix_reversal_gcd_diff_necessary_pair_preserved hm2 hmn'
        · exact prefix_reversal_gcd_diff_necessary_pair_preserved (by omega) (le_refl n)
      rw [hgen] at hsub
      exact hK (le_antisymm le_top hsub)
    · have hk2 : k % 2 = 1 := by obtain ⟨c, hc⟩ := hdivk2; omega
      have hm2 : m % 2 = 1 := by obtain ⟨c, hc⟩ := hdivm2; omega
      set q : Fin n → ℕ := fun x => x.val % 2 with hq
      have hK : prefix_reversal_gcd_diff_necessary_fiber_rel q ≠ ⊤ := by
        refine prefix_reversal_gcd_diff_necessary_fiber_ne_top q
          (a := ⟨0, by omega⟩) (b := ⟨2, by omega⟩) (c := ⟨1, by omega⟩) ?_ ?_ ?_ ?_
        · show (0:ℕ)%2 = 2%2; norm_num
        · show (0:ℕ)%2 ≠ 1%2; norm_num
        · show (⟨2, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩; intro h; simp at h
        · show (⟨1, by omega⟩ : Fin n) ≠ ⟨0, by omega⟩; intro h; simp at h
      have hsub : Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} ≤
          prefix_reversal_gcd_diff_necessary_fiber_rel q := by
        rw [Subgroup.closure_le]
        intro g hg
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
        rcases hg with rfl | rfl | rfl
        · exact prefix_reversal_gcd_diff_necessary_parity_fiber hk2 hkn
        · exact prefix_reversal_gcd_diff_necessary_parity_fiber hm2 hmn'
        · exact prefix_reversal_gcd_diff_necessary_parity_fiber (by omega) (le_refl n)
      rw [hgen] at hsub
      exact hK (le_antisymm le_top hsub)
  · set S : Set (Fin n) :=
      {x : Fin n | (x.val : ZMod d) = 0 ∨ (x.val : ZMod d) = ((n - 1 : ℕ) : ZMod d)} with hS
    have hK : prefix_reversal_gcd_diff_necessary_stabilizer_set S ≠ ⊤ := by
      obtain ⟨y, hy0, hyt⟩ :=
        prefix_reversal_gcd_diff_necessary_exists_zmod_not_pair hd3 ((n - 1 : ℕ) : ZMod d)
      have hyv : y.val < n := by
        have h1 : y.val < d := prefix_reversal_gcd_diff_necessary_zmod_val_lt (by omega) y
        omega
      refine prefix_reversal_gcd_diff_necessary_stabilizer_set_ne_top S
        ⟨0, by omega⟩ ⟨y.val, hyv⟩ ?_ ?_
      · show ((0:ℕ) : ZMod d) = 0 ∨ ((0:ℕ) : ZMod d) = ((n - 1 : ℕ) : ZMod d)
        exact Or.inl (Nat.cast_zero)
      · show ¬ (((y.val : ℕ) : ZMod d) = 0 ∨ ((y.val : ℕ) : ZMod d) = ((n - 1 : ℕ) : ZMod d))
        rw [prefix_reversal_gcd_diff_necessary_cast_val (by omega) y]
        exact fun h => h.elim hy0 hyt
    have hsub : Subgroup.closure {prefixReversal n k, prefixReversal n m, prefixReversal n n} ≤
        prefix_reversal_gcd_diff_necessary_stabilizer_set S := by
      rw [Subgroup.closure_le]
      intro g hg
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
      rcases hg with rfl | rfl | rfl
      · exact prefix_reversal_gcd_diff_necessary_set_preserved hk1 hkn hn1 hdivk
      · exact prefix_reversal_gcd_diff_necessary_set_preserved hm1 hmn' hn1 hdivm
      · refine prefix_reversal_gcd_diff_necessary_set_preserved hn1 (le_refl n) hn1 ?_
        rw [Nat.sub_self]
        exact Nat.dvd_zero d
    rw [hgen] at hsub
    exact hK (le_antisymm le_top hsub)
