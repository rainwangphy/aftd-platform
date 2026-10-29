import AFTD.Prelude
import AFTD.Kb.Tcs.IsRigidSequence
import AFTD.Kb.Tcs.RigidSequenceTensorProduct

/-!
# not_rigid_sequence_product_zero_sum_free

Topic: combinatorics   Node: 165f7c95e462

Provenance: original. Related work: refutes `rigid_sequence_product_zero_sum_free`

The statement `rigid_sequence_product_zero_sum_free` is false: The statement is false for a = 1, m = 3, n = 6, t = 1, r(0) = 1 over G = Fin 1 → ZMod 6.

Let h : Fin 1 → ZMod 6 := fun _ => 1, and l : Fin 1 → ZMod 6 := fun _ => 4.
Let S(0) = replicate 5 h + replicate 1 l.

1. S(0) satisfies `is_rigid_sequence 6 3 (S 0)`:
- S(0) has cardinality 6 and sum 5 * 1 + 1 * 4 = 9 = 3 ≠ 0 in ZMod 6. Since card S(0) = 6, its only submultiset of size 6 is itself, which has non-zero sum. Thus S(0) has no 6-term zero-sum subsequence.
- The counts in S(0) are count(h) = 5 = 6 - 1 (heavy) and count(l) = 1 with 0 < 1 ≤ 3 - 1 = 2 (light).
- Any 6-term multiset supported on supp(S(0)) = {h, l} has the form h^k l^(6-k). Its sum is k * 1 + (6 - k) * 4 = 24 - 3k = -3k mod 6. For this to be 0 mod 6, k must be even:
  * k = 0: W = l^6 (form x^n)
  * k = 6: W = h^6 (form x^n)
  * k = 2: W = h^2 l^4 (form h^k l^(n-k) with 0 < 2 < 6)
  * k = 4: W = h^4 l^2 (form h^k l^(n-k) with 0 < 4 < 6).
Thus every 6-term zero-sum supported on S(0) satisfies the rigid sequence condition.

2. In `rigid_sequence_tensor_product 6 3 S`:
- For x_h := fun _ => h, coordinate 0 is heavy, so it has 0 light coordinates and multiplicity n - 1 = 5.
- For x_l := fun _ => l, coordinate 0 is light, so it has 1 light coordinate and multiplicity m - 1 = 2.

3. Consider W = replicate 4 x_h + replicate 2 x_l:
- W ≤ rigid_sequence_tensor_product 6 3 S because count(x_h, W) = 4 ≤ 5 and count(x_l, W) = 2 ≤ 2.
- W.card = 4 + 2 = 6 = n.
- W.sum = 4 • x_h + 2 • x_l = fun _ => fun _ => (4 * 1 + 2 * 4) = fun _ => fun _ => 12 = 0.
Thus W is a 6-term zero-sum subsequence of `rigid_sequence_tensor_product 6 3 S`, contradicting the theorem statement.
-/

private def not_rigid_sequence_product_zero_sum_free_h : Fin 1 → ZMod 6 := fun _ => 1

private def not_rigid_sequence_product_zero_sum_free_l : Fin 1 → ZMod 6 := fun _ => 4

private def not_rigid_sequence_product_zero_sum_free_S : Multiset (Fin 1 → ZMod 6) :=
  Multiset.replicate 5 not_rigid_sequence_product_zero_sum_free_h +
    Multiset.replicate 1 not_rigid_sequence_product_zero_sum_free_l

private def not_rigid_sequence_product_zero_sum_free_W : Multiset ((_ : Fin 1) → Fin 1 → ZMod 6) :=
  Multiset.replicate 4 (fun _ : Fin 1 => not_rigid_sequence_product_zero_sum_free_h) +
    Multiset.replicate 2 (fun _ : Fin 1 => not_rigid_sequence_product_zero_sum_free_l)

private lemma not_rigid_sequence_product_zero_sum_free_mem_iff (x : Fin 1 → ZMod 6) :
    x ∈ not_rigid_sequence_product_zero_sum_free_S ↔
      x = not_rigid_sequence_product_zero_sum_free_h ∨
        x = not_rigid_sequence_product_zero_sum_free_l := by
  simp only [not_rigid_sequence_product_zero_sum_free_S, Multiset.mem_add, Multiset.mem_replicate]
  constructor
  · rintro (⟨-, h⟩ | ⟨-, h⟩)
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact Or.inl ⟨by decide, rfl⟩
    · exact Or.inr ⟨by decide, rfl⟩

private lemma not_rigid_sequence_product_zero_sum_free_decomp
    (W : Multiset (Fin 1 → ZMod 6))
    (hW : ∀ x ∈ W, x = not_rigid_sequence_product_zero_sum_free_h ∨
      x = not_rigid_sequence_product_zero_sum_free_l) :
    W = Multiset.replicate (Multiset.count not_rigid_sequence_product_zero_sum_free_h W)
          not_rigid_sequence_product_zero_sum_free_h +
        Multiset.replicate (Multiset.count not_rigid_sequence_product_zero_sum_free_l W)
          not_rigid_sequence_product_zero_sum_free_l := by
  induction W using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    have ha : a = not_rigid_sequence_product_zero_sum_free_h ∨
        a = not_rigid_sequence_product_zero_sum_free_l := hW a (Multiset.mem_cons_self a s)
    have hs : ∀ x ∈ s, x = not_rigid_sequence_product_zero_sum_free_h ∨
        x = not_rigid_sequence_product_zero_sum_free_l :=
      fun x hx => hW x (Multiset.mem_cons_of_mem hx)
    have hih := ih hs
    rcases ha with rfl | rfl
    · simp only [Multiset.count_cons]
      simp only [if_neg (by decide : ¬ not_rigid_sequence_product_zero_sum_free_l =
        not_rigid_sequence_product_zero_sum_free_h), Nat.add_zero]
      conv_lhs => rw [hih]
      simp [Multiset.replicate_succ]
    · simp only [Multiset.count_cons]
      simp only [if_neg (by decide : ¬ not_rigid_sequence_product_zero_sum_free_h =
        not_rigid_sequence_product_zero_sum_free_l), Nat.add_zero]
      conv_lhs => rw [hih]
      simp [Multiset.replicate_succ]

private lemma not_rigid_sequence_product_zero_sum_free_rigid :
    is_rigid_sequence 6 3 not_rigid_sequence_product_zero_sum_free_S := by
  refine ⟨?_, ?_, ?_⟩
  · rintro ⟨W, hle, hcard, hsum⟩
    have hc : W = not_rigid_sequence_product_zero_sum_free_S :=
      Multiset.eq_of_le_of_card_le hle (by rw [hcard]; decide)
    rw [hc] at hsum
    exact absurd hsum (by decide)
  · intro x hx
    rcases (not_rigid_sequence_product_zero_sum_free_mem_iff x).1 hx with rfl | rfl
    · left; decide
    · right; decide
  · intro W hcard hsum hsupp
    have hall : ∀ x ∈ W, x = not_rigid_sequence_product_zero_sum_free_h ∨
        x = not_rigid_sequence_product_zero_sum_free_l :=
      fun x hx => (not_rigid_sequence_product_zero_sum_free_mem_iff x).1 (hsupp x hx)
    have hdec := not_rigid_sequence_product_zero_sum_free_decomp W hall
    have hcard' : Multiset.count not_rigid_sequence_product_zero_sum_free_h W +
        Multiset.count not_rigid_sequence_product_zero_sum_free_l W = 6 := by
      have h : (Multiset.replicate (Multiset.count not_rigid_sequence_product_zero_sum_free_h W)
            not_rigid_sequence_product_zero_sum_free_h +
          Multiset.replicate (Multiset.count not_rigid_sequence_product_zero_sum_free_l W)
            not_rigid_sequence_product_zero_sum_free_l).card = 6 := by
        rw [← hdec]; exact hcard
      simpa using h
    rcases Nat.eq_zero_or_pos (Multiset.count not_rigid_sequence_product_zero_sum_free_h W)
      with ha0 | hapos
    · left
      refine ⟨not_rigid_sequence_product_zero_sum_free_l,
        (not_rigid_sequence_product_zero_sum_free_mem_iff _).2 (Or.inr rfl), ?_⟩
      have hb : Multiset.count not_rigid_sequence_product_zero_sum_free_l W = 6 := by omega
      conv_lhs => rw [hdec, ha0, hb]
      simp
    · rcases Nat.lt_or_ge (Multiset.count not_rigid_sequence_product_zero_sum_free_h W) 6
        with hlt | hge
      · right
        refine ⟨not_rigid_sequence_product_zero_sum_free_h,
          not_rigid_sequence_product_zero_sum_free_l,
          Multiset.count not_rigid_sequence_product_zero_sum_free_h W,
          by decide, by decide, hapos, hlt, ?_⟩
        have hb : Multiset.count not_rigid_sequence_product_zero_sum_free_l W =
            6 - Multiset.count not_rigid_sequence_product_zero_sum_free_h W := by omega
        conv_lhs => rw [hdec, hb]
      · left
        refine ⟨not_rigid_sequence_product_zero_sum_free_h,
          (not_rigid_sequence_product_zero_sum_free_mem_iff _).2 (Or.inl rfl), ?_⟩
        have ha : Multiset.count not_rigid_sequence_product_zero_sum_free_h W = 6 := by omega
        have hb0 : Multiset.count not_rigid_sequence_product_zero_sum_free_l W = 0 := by omega
        conv_lhs => rw [hdec, ha, hb0]
        simp

theorem not_rigid_sequence_product_zero_sum_free : ¬ (∀ {a : ℕ} (ha : 1 ≤ a) {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m) {n : ℕ} (hn : n = 2 ^ a * m)
    {t : ℕ} (ht : 1 ≤ t) (r : Fin t → ℕ)
    (S : (i : Fin t) → Multiset (Fin (r i) → ZMod n))
    (hS : ∀ i, is_rigid_sequence n m (S i)), ¬ ∃ W : Multiset ((i : Fin t) → Fin (r i) → ZMod n),
      W ≤ rigid_sequence_tensor_product n m S ∧ W.card = n ∧ W.sum = 0) := by
  intro H
  refine H (a := 1) (ha := by norm_num) (m := 3) (hm := ⟨1, by norm_num⟩) (hm3 := by norm_num)
    (n := 6) (hn := by norm_num) (t := 1) (ht := by norm_num) (r := fun _ => 1)
    (S := fun _ => not_rigid_sequence_product_zero_sum_free_S)
    (hS := fun _ => not_rigid_sequence_product_zero_sum_free_rigid)
    ⟨not_rigid_sequence_product_zero_sum_free_W, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
