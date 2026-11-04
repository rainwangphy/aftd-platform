import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsHalvingPartition

/-!
# halving_partition_length_le

Topic: elementary_number_theory   Node: 419b1cc55a17

Provenance: formalization of a published result. Source: arXiv:2611.01243 Theorem 3

For every positive integer n and every halving partition p of n, the length of p is at most Nat.log 2 n + (Nat.digits 2 n).sum.
-/

lemma halving_partition_length_le_isChain_getElem {α : Type*} {R : α → α → Prop} {l : List α}
    (h : List.IsChain R l) (i : ℕ) (hi : i + 1 < l.length) : R l[i] l[i+1] := by
  induction h generalizing i with
  | nil => contradiction
  | singleton a =>
    simp only [List.length_singleton] at hi
    omega
  | cons_cons hab hchain ih =>
    cases i with
    | zero => exact hab
    | succ i =>
      rw [List.getElem_cons_succ, List.getElem_cons_succ]
      apply ih

lemma halving_partition_length_le_div_pow_div_two (n i : ℕ) :
    (n / 2 ^ (i + 1)) / 2 = n / 2 ^ (i + 1 + 1) := by
  rw [Nat.div_div_eq_div_mul, ← pow_succ]

lemma halving_partition_length_le_part_ge_div_pow_two (n : ℕ) (p : List ℕ)
    (hp : is_halving_partition n p) (i : ℕ) (hi : i < p.length) :
    n / 2 ^ (i + 1) ≤ p[i] := by
  dsimp [is_halving_partition] at hp
  rcases hp with ⟨hpos, hsum, hrest⟩
  cases p with
  | nil => contradiction
  | cons p1 pt =>
    rcases hrest with ⟨hp1, hchain⟩
    induction i with
    | zero =>
      simp only [zero_add, pow_one]
      rcases hp1 with rfl | rfl
      · exact le_rfl
      · exact Nat.div_le_div_right (Nat.le_succ n)
    | succ i ih =>
      have hi_lt : i < (p1 :: pt).length := by omega
      have ih_val := ih hi_lt
      have hrel := halving_partition_length_le_isChain_getElem hchain i (by omega)
      have hdiv_le : (p1 :: pt)[i] / 2 ≤ (p1 :: pt)[i + 1] := by
        rcases hrel with h1 | h2
        · rw [h1]
        · rw [h2]
          exact Nat.div_le_div_right (Nat.le_succ _)
      have h_trans : (n / 2 ^ (i + 1)) / 2 ≤ (p1 :: pt)[i] / 2 :=
        Nat.div_le_div_right ih_val
      rw [halving_partition_length_le_div_pow_div_two] at h_trans
      exact h_trans.trans hdiv_le

lemma halving_partition_length_le_list_sum_ge_length (l : List ℕ) (h : ∀ x ∈ l, 1 ≤ x) :
    l.length ≤ l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, List.sum_cons]
    have ha : 1 ≤ a := h a (List.mem_cons_self ..)
    have hl : l.length ≤ l.sum := ih (fun x hx => h x (List.mem_cons_of_mem a hx))
    omega

lemma halving_partition_length_le_sum_take_ge_sum_range (p : List ℕ) (f : ℕ → ℕ) (k : ℕ)
    (hk : k ≤ p.length) (h : ∀ (i : ℕ) (hi : i < p.length), i < k → f i ≤ p[i]) :
    ∑ i ∈ Finset.range k, f i ≤ (p.take k).sum := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    have hk' : k < p.length := by omega
    have htake := (List.take_concat_get' p k hk').symm
    rw [htake, List.sum_append, List.sum_singleton]
    have ih_le : ∑ i ∈ Finset.range k, f i ≤ (p.take k).sum := by
      apply ih (by omega)
      intro i hi_p hi_k
      exact h i hi_p (by omega)
    have hlast : f k ≤ p[k] := h k hk' (by omega)
    omega

lemma halving_partition_length_le_sum_div_pow_two_eq (n : ℕ) :
    ∑ i ∈ Finset.range (Nat.log 2 n), n / 2 ^ (i + 1) = n - (Nat.digits 2 n).sum := by
  have h := @Nat.sub_one_mul_sum_log_div_pow_eq_sub_sum_digits 2 n
  simp only [Nat.reduceSub, one_mul] at h
  rw [← h]
  rw [Finset.sum_range_succ]
  have hzero : n / 2 ^ (Nat.log 2 n).succ = 0 := by
    apply Nat.div_eq_of_lt
    exact Nat.lt_pow_succ_log_self (by decide) n
  rw [hzero, add_zero]

/-- Upper bound on the length of any halving partition of n by floor(log_2 n) + s_2(n). -/
theorem halving_partition_length_le (n : ℕ) (hn : 0 < n) (p : List ℕ)
    (hp : is_halving_partition n p) :
    p.length ≤ Nat.log 2 n + (Nat.digits 2 n).sum := by
  let h := Nat.log 2 n
  by_cases hlen : p.length ≤ h
  · omega
  have hh_le : h ≤ p.length := by omega
  have hp_sum : p.sum = n := hp.2.1
  have hp_pos : ∀ x ∈ p, 1 ≤ x := fun x hx => hp.1 x hx
  have hsplit : p.sum = (p.take h).sum + (p.drop h).sum := by
    rw [← List.sum_append, List.take_append_drop]
  have htake_ge : ∑ i ∈ Finset.range h, n / 2 ^ (i + 1) ≤ (p.take h).sum := by
    apply halving_partition_length_le_sum_take_ge_sum_range p (fun i => n / 2 ^ (i + 1)) h hh_le
    intro i hi _
    exact halving_partition_length_le_part_ge_div_pow_two n p hp i hi
  rw [halving_partition_length_le_sum_div_pow_two_eq n] at htake_ge
  have hdrop_ge : p.length - h ≤ (p.drop h).sum := by
    rw [← List.length_drop]
    apply halving_partition_length_le_list_sum_ge_length
    intro x hx
    exact hp_pos x (List.mem_of_mem_drop hx)
  have hdigits_le : (Nat.digits 2 n).sum ≤ n := Nat.digit_sum_le 2 n
  omega
