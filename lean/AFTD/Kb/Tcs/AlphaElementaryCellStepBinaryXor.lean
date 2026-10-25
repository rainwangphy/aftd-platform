import AFTD.Prelude
import AFTD.Kb.Tcs.AlphaElementaryCellStep
import AFTD.Kb.Tcs.AlphaBinaryPrefix
import AFTD.Kb.Tcs.AlphaBinaryPrefixAppend
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# alpha_elementary_cell_step_binary_xor

Topic: combinatorics   Node: 452e62c6a78c

Provenance: helper lemma. Run-length helpers for OP-392, arXiv:2610.24758, Conjecture 1; lexical sequences and elementary operations from arXiv:0810.5205, Definitions 1.1, Section 2, Theorem 3.1 and Corollary 3.3. No new research advance is claimed for these supporting statements.

An elementary operation changes exactly the boundary bit immediately before the untouched suffix.
-/

theorem alpha_elementary_cell_step_binary_xor_singleton (c : ℕ) :
    alpha_binary_prefix [c] = 2 ^ (c - 1) := by
  simp [alpha_binary_prefix]

theorem alpha_elementary_cell_step_binary_xor_two (c : ℕ) (hc : 1 ≤ c) :
    alpha_binary_prefix [c, 1] = 2 ^ c + 1 := by
  simp [alpha_binary_prefix]
  omega

theorem alpha_elementary_cell_step_binary_xor_lt_pow_sum (a : List ℕ)
    (ha : ∀ v ∈ a, 0 < v) : alpha_binary_prefix a < 2 ^ a.sum := by
  induction a with
  | nil => simp [alpha_binary_prefix]
  | cons x xs ih =>
    have hx : 0 < x := ha x (List.mem_cons_self ..)
    have hxs : ∀ v ∈ xs, 0 < v := fun v hv => ha v (List.mem_cons_of_mem _ hv)
    have hih := ih hxs
    rw [alpha_binary_prefix.eq_def]
    simp only [List.sum_cons]
    have hx1 : 1 ≤ x := hx
    calc 2 ^ (x - 1 + xs.sum) + alpha_binary_prefix xs
        < 2 ^ (x - 1 + xs.sum) + 2 ^ xs.sum := by omega
      _ = (2 ^ (x - 1) + 1) * 2 ^ xs.sum := by ring
      _ ≤ 2 ^ x * 2 ^ xs.sum := by
        apply Nat.mul_le_mul_right
        have h2 : 2 ^ (x - 1) + 1 ≤ 2 ^ x := by
          rcases Nat.exists_eq_succ_of_ne_zero (by omega : x ≠ 0) with ⟨y, rfl⟩
          simp only [Nat.succ_sub_one]
          rw [pow_succ]
          have := Nat.one_le_two_pow (n := y)
          nlinarith
        exact h2
      _ = 2 ^ (x + xs.sum) := by ring

theorem alpha_elementary_cell_step_binary_xor_xor_split (s P Q x y : ℕ)
    (hx : x < 2 ^ s) (hy : y < 2 ^ s) :
    (2 ^ s * P + x) ^^^ (2 ^ s * Q + y) = 2 ^ s * (P ^^^ Q) + (x ^^^ y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_xor]
  rw [Nat.testBit_two_pow_mul_add P hx j, Nat.testBit_two_pow_mul_add Q hy j]
  have hxy : x ^^^ y < 2 ^ s := Nat.xor_lt_two_pow hx hy
  rw [Nat.testBit_two_pow_mul_add (P ^^^ Q) hxy j]
  by_cases hj : j < s
  · rw [if_pos hj, if_pos hj, if_pos hj, Nat.testBit_xor]
  · rw [if_neg hj, if_neg hj, if_neg hj, Nat.testBit_xor]

theorem alpha_elementary_cell_step_binary_xor_shift (p u v suf : List ℕ)
    (hsum : u.sum = v.sum)
    (hmid : alpha_binary_prefix v = alpha_binary_prefix u + 1)
    (heven : Even (alpha_binary_prefix u))
    (hpos : 0 < u.sum)
    (hsuf : alpha_binary_prefix suf < 2 ^ suf.sum) :
    alpha_binary_prefix (p ++ u ++ suf) ^^^ alpha_binary_prefix (p ++ v ++ suf) = 2 ^ suf.sum := by
  have hpu : alpha_binary_prefix (p ++ u) = 2 ^ u.sum * alpha_binary_prefix p + alpha_binary_prefix u := by
    rw [alpha_binary_prefix_append]
  have hpv : alpha_binary_prefix (p ++ v) = 2 ^ u.sum * alpha_binary_prefix p + alpha_binary_prefix v := by
    rw [alpha_binary_prefix_append, hsum]
  have hX : alpha_binary_prefix (p ++ v) = alpha_binary_prefix (p ++ u) + 1 := by
    rw [hpu, hpv, hmid]; omega
  have hevenX : Even (alpha_binary_prefix (p ++ u)) := by
    rw [hpu]
    have h2 : Even (2 ^ u.sum) := by
      rw [Nat.even_pow]
      exact ⟨even_two, by omega⟩
    have h2m := Even.mul_right h2 (alpha_binary_prefix p)
    exact Even.add h2m heven
  have hxor : alpha_binary_prefix (p ++ u) ^^^ (alpha_binary_prefix (p ++ u) + 1) = 1 := by
    have h1 : alpha_binary_prefix (p ++ u) ^^^ 1 = alpha_binary_prefix (p ++ u) + 1 :=
      Nat.xor_one_of_even hevenX
    rw [← h1, ← Nat.xor_assoc]
    simp
  rw [alpha_binary_prefix_append (p ++ u) suf, alpha_binary_prefix_append (p ++ v) suf, hX]
  rw [alpha_elementary_cell_step_binary_xor_xor_split suf.sum (alpha_binary_prefix (p ++ u))
        (alpha_binary_prefix (p ++ u) + 1) (alpha_binary_prefix suf) (alpha_binary_prefix suf)
        hsuf hsuf]
  rw [hxor]
  simp

theorem alpha_elementary_cell_step_binary_xor_take_drop (a : List ℕ) (i : ℕ)
    (hi : i < a.length) :
    a = a.take i ++ [a.getD i 0] ++ a.drop (i + 1) := by
  conv_lhs => rw [← List.take_append_drop i a]
  rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem a 0 hi]
  simp

theorem alpha_elementary_cell_step_binary_xor_take_drop_two (a : List ℕ) (i : ℕ)
    (hi : i < a.length) (hpos : 0 < i) (hget : a.getD i 0 = 1) :
    a = a.take (i - 1) ++ [a.getD (i - 1) 0, 1] ++ a.drop (i + 1) := by
  have hlt : i - 1 < a.length := by omega
  have htake : a.take i = a.take (i - 1) ++ [a.getD (i - 1) 0] := by
    rw [List.getD_eq_getElem a 0 hlt, List.take_append_getElem hlt,
      Nat.sub_add_cancel (by omega : 1 ≤ i)]
  conv_lhs => rw [alpha_elementary_cell_step_binary_xor_take_drop a i hi, hget, htake]
  simp only [List.append_assoc, List.cons_append, List.nil_append]

theorem alpha_elementary_cell_step_binary_xor (a b : List ℕ) (i : ℕ) (ha : ∀ v ∈ a, 0 < v) (h : alpha_elementary_cell_step a b i) : alpha_binary_prefix a ^^^ alpha_binary_prefix b = 2 ^ (a.drop (i + 1)).sum := by
  rcases h with ⟨hi, hsplit | hconj⟩
  · rcases hsplit with ⟨hc, hb⟩
    have hdecomp := alpha_elementary_cell_step_binary_xor_take_drop a i hi
    have hga : alpha_binary_prefix a
        = alpha_binary_prefix (a.take i ++ [a.getD i 0] ++ a.drop (i + 1)) := by
      conv_lhs => rw [hdecomp]
    rw [hga, hb]
    refine alpha_elementary_cell_step_binary_xor_shift (a.take i) [a.getD i 0]
      [a.getD i 0 - 1, 1] (a.drop (i + 1)) ?_ ?_ ?_ ?_ ?_
    · simp only [List.sum_cons, List.sum_nil, add_zero]
      omega
    · rw [alpha_elementary_cell_step_binary_xor_singleton,
        alpha_elementary_cell_step_binary_xor_two (a.getD i 0 - 1) (by omega)]
    · rw [alpha_elementary_cell_step_binary_xor_singleton, Nat.even_pow]
      exact ⟨even_two, by omega⟩
    · simp only [List.sum_cons, List.sum_nil, add_zero]
      omega
    · exact alpha_elementary_cell_step_binary_xor_lt_pow_sum _
        (fun v hv => ha v (List.mem_of_mem_drop hv))
  · rcases hconj with ⟨hpos, hget, hb⟩
    have hlt : i - 1 < a.length := by omega
    have hdpos : 0 < a.getD (i - 1) 0 := by
      rw [List.getD_eq_getElem a 0 hlt]
      exact ha _ (List.getElem_mem hlt)
    have hdecomp := alpha_elementary_cell_step_binary_xor_take_drop_two a i hi hpos hget
    have hga : alpha_binary_prefix a
        = alpha_binary_prefix (a.take (i - 1) ++ [a.getD (i - 1) 0, 1] ++ a.drop (i + 1)) := by
      conv_lhs => rw [hdecomp]
    rw [hga, hb, Nat.xor_comm]
    refine alpha_elementary_cell_step_binary_xor_shift (a.take (i - 1)) [a.getD (i - 1) 0 + 1]
      [a.getD (i - 1) 0, 1] (a.drop (i + 1)) ?_ ?_ ?_ ?_ ?_
    · simp only [List.sum_cons, List.sum_nil, add_zero]
    · rw [alpha_elementary_cell_step_binary_xor_two (a.getD (i - 1) 0) (by omega),
        alpha_elementary_cell_step_binary_xor_singleton]
      have hd : a.getD (i - 1) 0 + 1 - 1 = a.getD (i - 1) 0 := by omega
      rw [hd]
    · rw [alpha_elementary_cell_step_binary_xor_singleton, Nat.even_pow]
      constructor
      · exact even_two
      · omega
    · simp only [List.sum_cons, List.sum_nil, add_zero]
      omega
    · exact alpha_elementary_cell_step_binary_xor_lt_pow_sum _
        (fun v hv => ha v (List.mem_of_mem_drop hv))
