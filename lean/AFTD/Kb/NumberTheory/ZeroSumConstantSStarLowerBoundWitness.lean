import AFTD.Prelude

/-!
# zero_sum_constant_s_star_lower_bound_witness

Topic: elementary_number_theory   Node: 89a3278f859a

Provenance: helper lemma. scout/2611-14248-the-zero-sum-constant-mathsf-s-p-and-inverse-problem.md:2441

For every odd prime $p$, there exists a multiset $W$ of size $2p$ of units in $\mathbb{Z}/p^2\mathbb{Z}$ that has no sub-multiset $T \le W$ of cardinality $p$ with `(T.sum : ZMod (p^2)).val % p = 0` and `(T.sum : ZMod (p^2)).val % p^2 ≠ 0`.
-/

theorem multiset_eq_of_le_card_eq {α : Type*} (s t : Multiset α) (hle : s ≤ t) (hcard : s.card = t.card) : s = t := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp hle
  rw [Multiset.card_add] at hcard
  have : u.card = 0 := by omega
  rw [Multiset.card_eq_zero.mp this, add_zero]

theorem map_const_of_forall_mem {α β : Type*} (s : Multiset α) (c : β) (g : α → β)
    (h : ∀ x ∈ s, g x = c) :
    s.map g = Multiset.replicate s.card c := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.card_cons, Multiset.replicate_succ]
    have ha : g a = c := h a (Multiset.mem_cons_self a s)
    rw [ha]
    congr 1
    apply ih
    intro x hx
    exact h x (Multiset.mem_cons_of_mem hx)

/-- Existence of an exceptional sequence of length 2p of units in ZMod (p^2), witnessing the lower bound s_p^* >= 2p + 1. -/
theorem zero_sum_constant_s_star_lower_bound_witness (p : ℕ) (hp : p.Prime) (hp_odd : p ≠ 2) :
    ∃ W : Multiset (ZMod (p ^ 2)), W.card = 2 * p ∧ (∀ x ∈ W, IsUnit x) ∧
      ¬ ∃ T ≤ W, T.card = p ∧ T.sum.val % p = 0 ∧ T.sum.val % p ^ 2 ≠ 0 := by
  let h_dvd : p ∣ p ^ 2 := dvd_pow_self p (by decide)
  let f : ZMod (p ^ 2) →+* ZMod p := ZMod.castHom h_dvd (ZMod p)
  let A : Multiset (ZMod (p ^ 2)) := Multiset.replicate (p - 1) 1 + {1 - (p : ZMod (p ^ 2))}
  let B : Multiset (ZMod (p ^ 2)) := Multiset.replicate (p - 1) (-1) + {(p : ZMod (p ^ 2)) - 1}
  let W := A + B
  use W
  have hA_card : A.card = p := by
    dsimp [A]
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
    exact Nat.sub_add_cancel hp.pos
  have hB_card : B.card = p := by
    dsimp [B]
    simp only [Multiset.card_add, Multiset.card_replicate, Multiset.card_singleton]
    exact Nat.sub_add_cancel hp.pos
  have hW_card : W.card = 2 * p := by
    dsimp [W]
    rw [Multiset.card_add, hA_card, hB_card]
    ring
  refine ⟨hW_card, ?_, ?_⟩
  · intro x hx
    have h_unit_one : IsUnit (1 : ZMod (p ^ 2)) := isUnit_one
    have h_unit_neg_one : IsUnit (-1 : ZMod (p ^ 2)) := isUnit_one.neg
    have h_inv : (1 - (p : ZMod (p ^ 2))) * (1 + (p : ZMod (p ^ 2))) = 1 := by
      have : (p : ZMod (p ^ 2)) ^ 2 = 0 := by
        rw [← Nat.cast_pow, ZMod.natCast_self]
      linear_combination -this
    have h_unit_1_sub_p : IsUnit (1 - (p : ZMod (p ^ 2))) :=
      isUnit_of_dvd_one ⟨1 + (p : ZMod (p ^ 2)), h_inv.symm⟩
    have h_unit_p_sub_1 : IsUnit ((p : ZMod (p ^ 2)) - 1) := by
      have : (p : ZMod (p ^ 2)) - 1 = - (1 - (p : ZMod (p ^ 2))) := by ring
      rw [this]
      exact h_unit_1_sub_p.neg
    dsimp [W, A, B] at hx
    rw [Multiset.mem_add] at hx
    rcases hx with hx | hx
    · rw [Multiset.mem_add] at hx
      rcases hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]; exact h_unit_one
      · rw [Multiset.mem_singleton.mp hx]; exact h_unit_1_sub_p
    · rw [Multiset.mem_add] at hx
      rcases hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]; exact h_unit_neg_one
      · rw [Multiset.mem_singleton.mp hx]; exact h_unit_p_sub_1
  · rintro ⟨T, hTW, hT_card, hT_p, hT_p2⟩
    have hA_sum : A.sum = 0 := by
      dsimp [A]
      rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton]
      simp only [nsmul_eq_mul, mul_one]
      have h1 : ((p - 1 : ℕ) : ZMod (p ^ 2)) + 1 = (p : ZMod (p ^ 2)) := by
        rw [← Nat.cast_add_one, Nat.sub_add_cancel hp.pos]
      linear_combination h1
    have hB_sum : B.sum = 0 := by
      dsimp [B]
      rw [Multiset.sum_add, Multiset.sum_replicate, Multiset.sum_singleton]
      simp only [nsmul_eq_mul, mul_neg, mul_one]
      have h1 : ((p - 1 : ℕ) : ZMod (p ^ 2)) + 1 = (p : ZMod (p ^ 2)) := by
        rw [← Nat.cast_add_one, Nat.sub_add_cancel hp.pos]
      linear_combination -h1
    have hfA : ∀ x ∈ A, f x = 1 := by
      intro x hx
      have h1 : f 1 = 1 := by simp [f]
      have h2 : f (1 - (p : ZMod (p ^ 2))) = 1 := by simp [f]
      dsimp [A] at hx
      rw [Multiset.mem_add] at hx
      rcases hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]; exact h1
      · rw [Multiset.mem_singleton.mp hx]; exact h2
    have hfB : ∀ x ∈ B, f x = -1 := by
      intro x hx
      have h3 : f (-1) = -1 := by simp [f]
      have h4 : f ((p : ZMod (p ^ 2)) - 1) = -1 := by simp [f]
      dsimp [B] at hx
      rw [Multiset.mem_add] at hx
      rcases hx with hx | hx
      · rw [Multiset.eq_of_mem_replicate hx]; exact h3
      · rw [Multiset.mem_singleton.mp hx]; exact h4
    have h2_ne_0 : (2 : ZMod p) ≠ 0 := by
      intro h
      have : (2 : ZMod p) = ((2 : ℕ) : ZMod p) := rfl
      rw [this, ZMod.natCast_eq_zero_iff] at h
      have : p ≤ 2 := Nat.le_of_dvd (by decide) h
      have : p ≥ 2 := hp.two_le
      omega
    have hneg1_ne_1 : (-1 : ZMod p) ≠ 1 := by
      intro h
      have : (2 : ZMod p) = 0 := by linear_combination -h
      exact h2_ne_0 this
    let TA := T.filter (fun x => f x = 1)
    let TB := T.filter (fun x => f x ≠ 1)
    have hTA_le : TA ≤ A := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ TA
      · have hfx : f x = 1 := (Multiset.mem_filter.mp hx).2
        have hxB : x ∉ B := by
          intro h
          have := hfB x h
          rw [this] at hfx
          exact hneg1_ne_1 hfx
        have hxB_count : B.count x = 0 := Multiset.count_eq_zero.mpr hxB
        have hle := Multiset.count_le_of_le x (Multiset.filter_le (fun x => f x = 1) T)
        have hle2 := Multiset.count_le_of_le x hTW
        rw [Multiset.count_add, hxB_count, add_zero] at hle2
        exact hle.trans hle2
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have hTB_le : TB ≤ B := by
      rw [Multiset.le_iff_count]
      intro x
      by_cases hx : x ∈ TB
      · have hfx : f x ≠ 1 := (Multiset.mem_filter.mp hx).2
        have hxA : x ∉ A := by
          intro h
          exact hfx (hfA x h)
        have hxA_count : A.count x = 0 := Multiset.count_eq_zero.mpr hxA
        have hle := Multiset.count_le_of_le x (Multiset.filter_le (fun x => f x ≠ 1) T)
        have hle2 := Multiset.count_le_of_le x hTW
        rw [Multiset.count_add, hxA_count, zero_add] at hle2
        exact hle.trans hle2
      · rw [Multiset.count_eq_zero.mpr hx]
        exact Nat.zero_le _
    have hT_decomp : T = TA + TB := by
      exact (Multiset.filter_add_not (fun x => f x = 1) T).symm
    have h_cards : TA.card + TB.card = p := by
      rw [← Multiset.card_add, ← hT_decomp, hT_card]
    have hTA_map : TA.map f = Multiset.replicate TA.card 1 :=
      map_const_of_forall_mem TA 1 f (fun x hx => (Multiset.mem_filter.mp hx).2)
    have hTB_map : TB.map f = Multiset.replicate TB.card (-1) :=
      map_const_of_forall_mem TB (-1) f (fun x hx => hfB x (Multiset.mem_of_le hTB_le hx))
    have hT_map_sum : (T.map f).sum = (TA.card : ZMod p) - (TB.card : ZMod p) := by
      rw [hT_decomp, Multiset.map_add, Multiset.sum_add, hTA_map, hTB_map]
      simp only [Multiset.sum_replicate, nsmul_eq_mul, mul_one, mul_neg]
      ring
    have h_TB_card : (TB.card : ZMod p) = - (TA.card : ZMod p) := by
      have : ((TA.card + TB.card : ℕ) : ZMod p) = (p : ZMod p) := by rw [h_cards]
      push_cast at this
      rw [ZMod.natCast_self] at this
      linear_combination this
    have hT_sum_zero : f T.sum = 0 := by
      have : f T.sum = (T.sum.val : ZMod p) := by
        rw [ZMod.castHom_apply]
        have : NeZero (p ^ 2) := ⟨pow_ne_zero 2 hp.ne_zero⟩
        exact ZMod.cast_eq_val T.sum
      rw [this, ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero]
      exact hT_p
    have h_2TA : 2 * (TA.card : ZMod p) = 0 := by
      have h1 : (T.map f).sum = 0 := (map_multiset_sum f T).symm.trans hT_sum_zero
      calc 2 * (TA.card : ZMod p) = (TA.card : ZMod p) - (- (TA.card : ZMod p)) := by ring
      _ = (TA.card : ZMod p) - (TB.card : ZMod p) := by rw [← h_TB_card]
      _ = (T.map f).sum := hT_map_sum.symm
      _ = 0 := h1
    have hTA_zero : (TA.card : ZMod p) = 0 := by
      have : Fact p.Prime := ⟨hp⟩
      cases mul_eq_zero.mp h_2TA with
      | inl h => exact False.elim (h2_ne_0 h)
      | inr h => exact h
    rw [ZMod.natCast_eq_zero_iff, Nat.dvd_iff_mod_eq_zero] at hTA_zero
    have hTA_le_p : TA.card ≤ p := (Multiset.card_le_card hTA_le).trans_eq hA_card
    have hTA_cases : TA.card = 0 ∨ TA.card = p := by
      rcases Nat.eq_zero_or_pos TA.card with h | h
      · left; exact h
      · right
        have := Nat.le_of_dvd h (Nat.dvd_of_mod_eq_zero hTA_zero)
        omega
    have hT_sum_eq_zero : T.sum = 0 := by
      rcases hTA_cases with h0 | hp_eq
      · have hTA_empty : TA = 0 := Multiset.card_eq_zero.mp h0
        rw [hTA_empty, zero_add] at hT_decomp
        have hTB_eq : TB = B := multiset_eq_of_le_card_eq TB B hTB_le (by omega)
        rw [hTB_eq] at hT_decomp
        rw [hT_decomp, hB_sum]
      · have hTB_zero : TB.card = 0 := by omega
        have hTB_empty : TB = 0 := Multiset.card_eq_zero.mp hTB_zero
        rw [hTB_empty, add_zero] at hT_decomp
        have hTA_eq : TA = A := multiset_eq_of_le_card_eq TA A hTA_le (by omega)
        rw [hTA_eq] at hT_decomp
        rw [hT_decomp, hA_sum]
    have : T.sum.val % p ^ 2 = 0 := by
      rw [hT_sum_eq_zero, ZMod.val_zero, Nat.zero_mod]
    exact hT_p2 this
