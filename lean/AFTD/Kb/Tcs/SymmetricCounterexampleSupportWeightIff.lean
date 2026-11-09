import AFTD.Prelude
import AFTD.Kb.Tcs.SymmetricCounterexampleFunc
import AFTD.Kb.Tcs.Weight

/-!
# symmetric_counterexample_support_weight_iff

Topic: combinatorics   Node: 4d1e2d4d77eb

Provenance: formalization of a published result. Source: arXiv:2611.06744, Lemma 6

For any n = 2^k ≥ 8 and any input v : Fin n → ZMod 2, the symmetric Boolean function symmetric_counterexample_func n evaluates to 1 on v if and only if the Hamming weight of v is at most 1 or at least n / 2 + 2.
-/

private lemma symmetric_counterexample_support_weight_iff_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x; decide

/-- Parity of `choose (2 ^ k)`: it agrees modulo two with `t / 2 ^ k`. -/
private lemma symmetric_counterexample_support_weight_iff_choose_two_pow_cast_eq (k t : ℕ) :
    ((t.choose (2 ^ k) : ℕ) : ZMod 2) = ((t / 2 ^ k : ℕ) : ZMod 2) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    have hstep : t.choose (2 ^ (k + 1)) ≡ (t / 2).choose (2 ^ k) [MOD 2] := by
      have h := Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := t) (k := 2 ^ (k + 1)) (p := 2)
      have h1 : 2 ^ (k + 1) % 2 = 0 := by rw [pow_succ]; simp
      have h2 : 2 ^ (k + 1) / 2 = 2 ^ k := by rw [pow_succ]; simp
      rw [h1, h2, Nat.choose_zero_right, one_mul] at h
      exact h
    have hih : (t / 2).choose (2 ^ k) ≡ (t / 2) / 2 ^ k [MOD 2] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      exact ih (t / 2)
    have hfin : (t / 2) / 2 ^ k = t / 2 ^ (k + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ, Nat.mul_comm]
    rw [ZMod.natCast_eq_natCast_iff, ← hfin]
    exact hstep.trans hih

/-- `choose t (2 ^ j)` is odd exactly when `2 ^ j ≤ t`, for `t < 2 ^ (j+1)`. -/
private lemma symmetric_counterexample_support_weight_iff_choose_two_pow_cast_eq_one_iff (j t : ℕ)
    (ht : t < 2 ^ (j + 1)) :
    ((t.choose (2 ^ j) : ℕ) : ZMod 2) = 1 ↔ 2 ^ j ≤ t := by
  rw [symmetric_counterexample_support_weight_iff_choose_two_pow_cast_eq]
  have hN : 0 < 2 ^ j := pow_pos (by norm_num) j
  have ht' : t < 2 * 2 ^ j := by rw [pow_succ] at ht; omega
  have hlt : t / 2 ^ j < 2 := by rw [Nat.div_lt_iff_lt_mul hN]; exact ht'
  have hq : t / 2 ^ j = 0 ∨ t / 2 ^ j = 1 := by
    have h1 : t / 2 ^ j ≤ 1 := Nat.lt_succ_iff.mp hlt
    rcases Nat.eq_zero_or_pos (t / 2 ^ j) with h | h
    · exact Or.inl h
    · exact Or.inr (Nat.le_antisymm h1 (Nat.succ_le_of_lt h))
  rcases hq with h0 | h1
  · rw [h0]
    constructor
    · intro hc; exact absurd hc (by decide)
    · intro hle
      exfalso
      have hone : 1 ≤ t / 2 ^ j := by rw [Nat.one_le_div_iff hN]; exact hle
      omega
  · rw [h1]
    constructor
    · intro _
      have h1le : 1 ≤ t / 2 ^ j := le_of_eq h1.symm
      rw [Nat.one_le_div_iff hN] at h1le
      exact h1le
    · intro _; norm_num

/-- Double Pascal identity modulo two: `choose w (d+2) ≡ choose (w-2) (d+2) + choose (w-2) d`. -/
private lemma symmetric_counterexample_support_weight_iff_choose_add_two_cast (w d : ℕ) (hw : 2 ≤ w) :
    ((w.choose (d + 2) : ℕ) : ZMod 2) = ((w - 2).choose (d + 2) : ℕ) + ((w - 2).choose d : ℕ) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 2 := ⟨w - 2, by omega⟩
  have h1 : (w' + 2).choose (d + 2) = (w' + 1).choose (d + 1) + (w' + 1).choose (d + 2) := by
    simpa using Nat.choose_succ_succ (w' + 1) (d + 1)
  have h2 : (w' + 1).choose (d + 1) = (w').choose d + (w').choose (d + 1) := by
    simpa using Nat.choose_succ_succ w' d
  have h3 : (w' + 1).choose (d + 2) = (w').choose (d + 1) + (w').choose (d + 2) := by
    simpa using Nat.choose_succ_succ w' (d + 1)
  have key : (w' + 2).choose (d + 2) = (w').choose (d + 2) + (w').choose d + 2 * (w').choose (d + 1) := by
    rw [h1, h2, h3]; ring
  show ((w' + 2).choose (d + 2) : ZMod 2) = ((w' + 2 - 2).choose (d + 2) : ZMod 2) + ((w' + 2 - 2).choose d : ZMod 2)
  simp only [Nat.add_sub_cancel]
  have h2z : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
  rw [key]
  push_cast
  rw [h2z, zero_mul, add_zero]

/-- Telescoped even-indexed binomial sum modulo two. -/
private lemma symmetric_counterexample_support_weight_iff_sum_choose_even_cast (M w : ℕ) (hw : 2 ≤ w) :
    (∑ j ∈ Finset.range (M + 1), ((w.choose (2 * j) : ℕ) : ZMod 2)) = ((w - 2).choose (2 * M) : ℕ) := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [Finset.sum_range_succ, ih]
    have h := symmetric_counterexample_support_weight_iff_choose_add_two_cast w (2 * M) hw
    have e : 2 * (M + 1) = 2 * M + 2 := by ring
    rw [e, h]
    have h2z : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    have eq : ((w - 2).choose (2 * M) : ZMod 2) + (((w - 2).choose (2 * M + 2) : ZMod 2) + ((w - 2).choose (2 * M) : ZMod 2))
        = ((w - 2).choose (2 * M + 2) : ZMod 2) + 2 * ((w - 2).choose (2 * M) : ZMod 2) := by ring
    rw [eq, h2z, zero_mul, add_zero]

/-- For very small weight the sum of even binomial coefficients is one. -/
private lemma symmetric_counterexample_support_weight_iff_sum_small (M w : ℕ) (hw : w ≤ 1) :
    (∑ j ∈ Finset.range (M + 1), ((w.choose (2 * j) : ℕ) : ZMod 2)) = 1 := by
  rw [Finset.sum_range_succ']
  have hzero : ∀ j : ℕ, ((w.choose (2 * (j + 1)) : ℕ) : ZMod 2) = 0 := by
    intro j
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    simp
  rw [Finset.sum_eq_zero (fun j _ => hzero j)]
  simp

/-- The elementary symmetric sum of degree `d` evaluated at `v` is `choose (weight v) d` mod two. -/
private lemma symmetric_counterexample_support_weight_iff_inner (n : ℕ) (v : Fin n → ZMod 2) (d : ℕ) :
    (∑ s ∈ Finset.powersetCard d Finset.univ, ∏ i ∈ s, v i)
      = (((Finset.univ.filter (fun i => v i = 1)).card.choose d : ℕ) : ZMod 2) := by
  classical
  set S := Finset.univ.filter (fun i => v i = 1) with hS
  have hmem : ∀ i, i ∈ S ↔ v i = 1 := by intro i; simp [hS]
  have hval : ∀ i, v i = if i ∈ S then (1 : ZMod 2) else 0 := by
    intro i
    by_cases h : i ∈ S
    · rw [if_pos h]; exact (hmem i).mp h
    · rw [if_neg h]
      rcases symmetric_counterexample_support_weight_iff_zero_or_one (v i) with h0 | h1
      · exact h0
      · exact absurd h1 (fun hv => h ((hmem i).mpr hv))
  have hprod : ∀ s : Finset (Fin n), (∏ i ∈ s, v i) = if s ⊆ S then (1:ZMod 2) else 0 := by
    intro s
    simp only [hval]
    rw [Finset.prod_boole]
    simp [Finset.subset_iff]
  have hfilt : (Finset.powersetCard d Finset.univ).filter (fun s => s ⊆ S) = S.powersetCard d := by
    ext s
    simp [Finset.mem_powersetCard, and_comm]
  calc (∑ s ∈ Finset.powersetCard d Finset.univ, ∏ i ∈ s, v i)
      = ∑ s ∈ Finset.powersetCard d Finset.univ, (if s ⊆ S then (1:ZMod 2) else 0) := by
        exact Finset.sum_congr rfl (fun s _ => hprod s)
    _ = (((Finset.powersetCard d Finset.univ).filter (fun s => s ⊆ S)).card : ZMod 2) := Finset.sum_boole _ _
    _ = ((S.powersetCard d).card : ZMod 2) := by rw [hfilt]
    _ = ((S.card.choose d : ℕ) : ZMod 2) := by rw [Finset.card_powersetCard]

/-- The value of `symmetric_counterexample_func n` at `v` depends only on the Hamming weight. -/
private lemma symmetric_counterexample_support_weight_iff_func_eq_sum (n : ℕ) (v : Fin n → ZMod 2) :
    symmetric_counterexample_func n v
      = ∑ j ∈ Finset.range (n / 4 + 1), (((Finset.univ.filter (fun i => v i = 1)).card.choose (2 * j) : ℕ) : ZMod 2) := by
  rw [symmetric_counterexample_func]
  exact Finset.sum_congr rfl (fun j _ => symmetric_counterexample_support_weight_iff_inner n v (2 * j))

/-- Support of the symmetric counterexample function F_n in terms of Hamming weight. -/
theorem symmetric_counterexample_support_weight_iff (n : ℕ) (k : ℕ) (hn : n = 2 ^ k) (hn8 : 8 ≤ n) (v : Fin n → ZMod 2) : symmetric_counterexample_func n v = 1 ↔ (Finset.filter (fun i => v i = 1) Finset.univ).card ≤ 1 ∨ n / 2 + 2 ≤ (Finset.filter (fun i => v i = 1) Finset.univ).card := by
  classical
  set w := (Finset.filter (fun i => v i = 1) Finset.univ).card with hwdef
  have hk3 : 3 ≤ k := by
    have h : 2 ^ (3:ℕ) ≤ 2 ^ k := by
      rw [show (2:ℕ) ^ 3 = 8 from by norm_num, ← hn]
      exact hn8
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h
  have hn2 : n / 2 = 2 ^ (k - 1) := by
    rw [hn]
    exact Nat.pow_div (x := 2) (n := 1) (m := k) (by omega) (by norm_num)
  have hn4 : n / 4 = 2 ^ (k - 2) := by
    rw [hn]
    exact Nat.pow_div (x := 2) (n := 2) (m := k) (by omega) (by norm_num)
  have h2M : 2 * (n / 4) = n / 2 := by
    rw [hn4, hn2, show k - 1 = (k - 2) + 1 from by omega, pow_succ]
    ring
  have hwle : w ≤ n := by
    rw [hwdef]
    simpa using Finset.card_filter_le Finset.univ (fun i : Fin n => v i = 1)
  rw [symmetric_counterexample_support_weight_iff_func_eq_sum]
  by_cases hw : w ≤ 1
  · rw [symmetric_counterexample_support_weight_iff_sum_small (n / 4) w hw]
    simp [hw]
  · push Not at hw
    have hkey : ((∑ j ∈ Finset.range (n / 4 + 1), ((w.choose (2 * j) : ℕ) : ZMod 2)) = 1 ↔ n / 2 + 2 ≤ w) := by
      rw [symmetric_counterexample_support_weight_iff_sum_choose_even_cast (n / 4) w hw, h2M, hn2]
      rw [symmetric_counterexample_support_weight_iff_choose_two_pow_cast_eq_one_iff (k - 1) (w - 2)
        (by rw [show k - 1 + 1 = k from by omega, ← hn]; omega)]
      constructor
      · intro h; omega
      · intro h; omega
    rw [hkey]
    constructor
    · intro h; exact Or.inr h
    · intro h; rcases h with h | h
      · omega
      · exact h
