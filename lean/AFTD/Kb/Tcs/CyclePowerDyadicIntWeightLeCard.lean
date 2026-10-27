import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_dyadic_int_weight_le_card

Topic: combinatorics   Node: cbc138fb4a6c

Provenance: helper lemma. Uniform graph-to-class-model bridge for OP-205 / RT-1 following arXiv:2610.15635. Transfers the proved Boolean dyadic-tree weight certificate to finite integer sets; no research advance is claimed.

For a finite integer set of diameter at most 2^m-1, weight its endpoint-distance pairs by two and its other dyadic long-distance pairs by one. The total weight is at most its size, uniformly in m.
-/

private lemma cycle_power_dyadic_int_weight_le_card_count (N d : ℕ) (S : Finset ℤ) (c : ℤ) (b : ℕ → Bool)
    (hN : 1 ≤ N) (hd : d ≤ N)
    (hb : ∀ i, b i = true ↔ ((i:ℤ) + c) ∈ S)
    (hmin : ∀ x ∈ S, c ≤ x) (hbound : ∀ x ∈ S, x ≤ c + ((N - 1 : ℕ) : ℤ)) :
    (∑ e ∈ S, (if e + (d : ℤ) ∈ S then 1 else 0)) =
      (Finset.range (N - d)).sum (fun i => (b i && b (i + d)).toNat) := by
  classical
  have hleft : (∑ e ∈ S, (if e + (d : ℤ) ∈ S then 1 else 0))
      = (S.filter (fun e => e + (d : ℤ) ∈ S)).card := by
    rw [Finset.card_filter]
  have hright : (Finset.range (N - d)).sum (fun i => (b i && b (i + d)).toNat)
      = ((Finset.range (N - d)).filter (fun i => (b i && b (i + d)) = true)).card := by
    rw [Finset.card_filter]
    apply Finset.sum_congr rfl
    intro i hi
    cases b i <;> cases b (i + d) <;> simp
  rw [hleft, hright]
  apply Eq.symm
  refine Finset.card_bij (fun i hi => (i : ℤ) + c) ?_ ?_ ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true] at hi ⊢
    obtain ⟨hiN, hp, hq⟩ := hi
    have hbi : ((i:ℤ) + c) ∈ S := (hb i).mp hp
    have hb2 : (((i + d : ℕ) : ℤ) + c) ∈ S := (hb (i + d)).mp hq
    refine ⟨hbi, ?_⟩
    have heq : (i : ℤ) + c + (d : ℤ) = ((i + d : ℕ) : ℤ) + c := by push_cast; ring
    rw [heq]; exact hb2
  · intro i1 hi1 i2 hi2 heq
    have hZ : (i1 : ℤ) = (i2 : ℤ) := by linarith
    exact_mod_cast hZ
  · intro e he
    simp only [Finset.mem_filter] at he
    obtain ⟨heS, hedS⟩ := he
    have hce : 0 ≤ e - c := by linarith [hmin e heS]
    refine ⟨(e - c).toNat, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range, Bool.and_eq_true]
      have hcast : (((e - c).toNat : ℕ) : ℤ) = e - c := Int.toNat_of_nonneg hce
      have hlt : (e - c).toNat < N - d := by
        rw [Int.toNat_lt hce, Nat.cast_sub hd]
        have hb' := hbound (e + (d : ℤ)) hedS
        have hN1 : ((N - 1 : ℕ) : ℤ) = (N:ℤ) - 1 := by
          rw [Nat.cast_sub hN]; norm_num
        rw [hN1] at hb'
        linarith
      refine ⟨hlt, ?_, ?_⟩
      · rw [hb]
        have : (((e - c).toNat : ℕ) : ℤ) + c = e := by rw [hcast]; ring
        exact this.symm ▸ heS
      · rw [hb]
        have hid : ((((e - c).toNat + d : ℕ)) : ℤ) + c = e + d := by
          push_cast; rw [hcast]; ring
        exact hid.symm ▸ hedS
    · show (((e - c).toNat : ℕ) : ℤ) + c = e
      have hcast : (((e - c).toNat : ℕ) : ℤ) = e - c := Int.toNat_of_nonneg hce
      rw [hcast]; ring

theorem cycle_power_dyadic_int_weight_le_card
    (m : ℕ) (hm : 1 ≤ m) (S : Finset ℤ)
    (hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ ((2 ^ m - 1 : ℕ) : ℤ)) :
    (∑ e ∈ S,
      (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ S then 1 else 0))) ≤ S.card := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hS
  · simp
  have hN : 1 ≤ 2^m := Nat.one_le_two_pow
  set c : ℤ := S.min' hS with hcdef
  have hc : c ∈ S := by rw [hcdef]; exact S.min'_mem hS
  have hmin : ∀ x ∈ S, c ≤ x := by
    intro x hx; rw [hcdef]; exact Finset.min'_le S x hx
  have hbound : ∀ x ∈ S, x ≤ c + ((2^m - 1 : ℕ) : ℤ) := by
    intro x hx
    have h := hdiam x hx c hc
    rw [abs_le] at h
    linarith [h.2]
  set b : ℕ → Bool := fun i => decide (((i:ℤ) + c) ∈ S) with hbdef
  have hb : ∀ i, b i = true ↔ ((i:ℤ) + c) ∈ S := by
    intro i; simp [hbdef]
  have hstep :
      (∑ e ∈ S, (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ S then 1 else 0)))
      = 2 * (∑ e ∈ S, (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0))
        + ∑ j ∈ Finset.range m, ∑ e ∈ S,
            (if j = 0 then 0 else if e + ((2^m - 2^j : ℕ):ℤ) ∈ S then 1 else 0) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_comm]
  have hA : (∑ e ∈ S, (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0))
      = (b 0 && b (2^m - 1)).toNat := by
    have h := cycle_power_dyadic_int_weight_le_card_count (2^m) (2^m - 1) S c b hN (Nat.sub_le _ _) hb hmin hbound
    rw [h]
    have hsub : 2^m - (2^m - 1) = 1 := Nat.sub_sub_self hN
    rw [hsub, Finset.sum_range_one]
    simp
  have hJ : ∀ j ∈ Finset.range m,
      (∑ e ∈ S, (if j = 0 then 0 else if e + ((2^m - 2^j : ℕ):ℤ) ∈ S then 1 else 0))
      = (if j = 0 then 0 else ∑ i ∈ Finset.range (2^j), (b i && b (i + (2^m - 2^j))).toNat) := by
    intro j hj
    by_cases hj0 : j = 0
    · subst hj0; simp
    · simp only [hj0, if_false]
      have hle : 2^j ≤ 2^m := Nat.pow_le_pow_right (by norm_num) (le_of_lt (Finset.mem_range.mp hj))
      have h := cycle_power_dyadic_int_weight_le_card_count (2^m) (2^m - 2^j) S c b hN (Nat.sub_le _ _) hb hmin hbound
      rw [h, Nat.sub_sub_self hle]
  have hEq :
      (∑ e ∈ S, (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ S then 1 else 0)))
      = cycle_power_dyadic_class_weight m b := by
    rw [hstep, hA]
    unfold cycle_power_dyadic_class_weight
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [hJ j hj]
    by_cases hj0 : j = 0
    · simp [hj0]
    · simp only [hj0, if_false]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Nat.add_sub_assoc (Nat.pow_le_pow_right (by norm_num) (le_of_lt (Finset.mem_range.mp hj)))]
  have hcard : (∑ i ∈ Finset.range (2^m), (b i).toNat) = S.card := by
    have h := cycle_power_dyadic_int_weight_le_card_count (2^m) 0 S c b hN (Nat.zero_le _) hb hmin hbound
    simp only [Nat.sub_zero, Nat.cast_zero, add_zero] at h
    have hS1 : (∑ e ∈ S, (if e ∈ S then 1 else 0)) = S.card := by simp
    have hb' : (∑ i ∈ Finset.range (2^m), (b i && b i).toNat)
        = ∑ i ∈ Finset.range (2^m), (b i).toNat := by
      apply Finset.sum_congr rfl; intro i hi; cases b i <;> rfl
    rw [hS1, hb'] at h
    exact h.symm
  calc
    (∑ e ∈ S, (2 * (if e + ((2 ^ m - 1 : ℕ) : ℤ) ∈ S then 1 else 0) +
        (Finset.range m).sum (fun j => if j = 0 then 0 else
          if e + ((2 ^ m - 2 ^ j : ℕ) : ℤ) ∈ S then 1 else 0)))
        = cycle_power_dyadic_class_weight m b := hEq
    _ ≤ ∑ i ∈ Finset.range (2^m), (b i).toNat := cycle_power_dyadic_class_weight_le m hm b
    _ = S.card := hcard
