import AFTD.Prelude
import AFTD.Kb.Tcs.PartitionA
import AFTD.Kb.Tcs.IsTIntersectingPartitionFamily
import AFTD.Kb.Tcs.PartitionAIsOneIntersecting
import AFTD.Kb.Tcs.PartitionNumber

/-!
# unrestricted_partition_family_four_intersecting_and_card

Topic: combinatorics   Node: a88ef5e710b7

Provenance: formalization of a published result. Source: arXiv:2610.01747 Proposition 6.1

For every natural number n ≥ 1, the family partition_A n of partitions of n is 1-intersecting (is_t_intersecting_partition_family 1 (partition_A n)), and its cardinality coerced to ℤ satisfies ((partition_A n).card : ℤ) = partition_number (n - 3 : ℤ) + partition_number (n - 4 : ℤ) + partition_number (n - 5 : ℤ) - partition_number (n - 6 : ℤ) - partition_number (n - 7 : ℤ) - partition_number (n - 8 : ℤ) + partition_number (n - 9 : ℤ).
-/

open Multiset Finset

def unrestricted_partition_family_four_intersecting_and_card_b2z (b : Bool) : ℤ := if b then 1 else 0

lemma unrestricted_partition_family_four_intersecting_and_card_bool_pie (x1 x2 x3 x4 : Bool) :
    unrestricted_partition_family_four_intersecting_and_card_b2z ((x1 && x2) || (x1 && x3) || (x1 && x4) || (x2 && x3 && x4)) =
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x2) +
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x3) +
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x4) -
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x2 && x3) -
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x2 && x4) -
      unrestricted_partition_family_four_intersecting_and_card_b2z (x1 && x3 && x4) +
      unrestricted_partition_family_four_intersecting_and_card_b2z (x2 && x3 && x4) := by
  revert x1 x2 x3 x4
  decide

lemma unrestricted_partition_family_four_intersecting_and_card_decide_mem_partition_A (n : ℕ) (p : Nat.Partition n) :
    let x1 := decide (1 ∈ p.parts)
    let x2 := decide (2 ∈ p.parts)
    let x3 := decide (3 ∈ p.parts)
    let x4 := decide (4 ∈ p.parts)
    decide (p ∈ partition_A n) = ((x1 && x2) || (x1 && x3) || (x1 && x4) || (x2 && x3 && x4)) := by
  intro x1 x2 x3 x4
  rw [Bool.eq_iff_iff]
  rw [decide_eq_true_iff]
  rw [partition_A, Finset.mem_filter]
  simp only [mem_univ, true_and]
  dsimp [x1, x2, x3, x4]
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_iff]
  tauto

lemma unrestricted_partition_family_four_intersecting_and_card_sum_b2z_decide_mem (n : ℕ) (s : Finset (Nat.Partition n)) :
    ∑ p : Nat.Partition n, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (p ∈ s)) = (s.card : ℤ) := by
  have h : ∀ p, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (p ∈ s)) = if p ∈ s then (1 : ℤ) else 0 := by
    intro p
    simp [unrestricted_partition_family_four_intersecting_and_card_b2z]
  simp_rw [h]
  rw [← Finset.sum_filter]
  simp

lemma unrestricted_partition_family_four_intersecting_and_card_multiset_sum_le_sum_of_le {s t : Multiset ℕ} (h : s ≤ t) : s.sum ≤ t.sum := by
  have : s + (t - s) = t := add_comm s (t - s) ▸ tsub_add_cancel_of_le h
  rw [← this, sum_add]
  omega

def unrestricted_partition_family_four_intersecting_and_card_submultisetPartitionEquiv {n : ℕ} (M : Multiset ℕ) (hpos : ∀ x ∈ M, 0 < x) (hsum : M.sum ≤ n) :
    {p : Nat.Partition n // M ≤ p.parts} ≃ Nat.Partition (n - M.sum) where
  toFun p := ⟨p.1.parts - M, fun hx => p.1.parts_pos (mem_of_le tsub_le_self hx), by
    have hle := p.2
    have hsum_eq : (p.1.parts - M).sum + M.sum = p.1.parts.sum := by
      rw [← sum_add, tsub_add_cancel_of_le hle]
    have hp := p.1.parts_sum
    omega⟩
  invFun q := ⟨⟨M + q.parts, fun hx => by
    rcases mem_add.mp hx with h | h
    · exact hpos _ h
    · exact q.parts_pos h, by
    rw [sum_add, q.parts_sum]
    omega⟩, le_add_right _ _⟩
  left_inv p := by
    apply Subtype.ext
    apply Nat.Partition.ext
    dsimp
    rw [add_comm]
    exact tsub_add_cancel_of_le p.2
  right_inv q := by
    apply Nat.Partition.ext
    dsimp
    exact add_tsub_cancel_left _ _

theorem unrestricted_partition_family_four_intersecting_and_card_card_partition_containing_multiset (n : ℕ) (M : Multiset ℕ) (hpos : ∀ x ∈ M, 0 < x) :
    ((Nat.card {p : Nat.Partition n // M ≤ p.parts} : ℤ)) = partition_number (n - (M.sum : ℤ)) := by
  rw [partition_number]
  split_ifs with h
  · have hle : M.sum ≤ n := by omega
    have htoNat : (n - (M.sum : ℤ)).toNat = n - M.sum := by omega
    rw [htoNat]
    have e := unrestricted_partition_family_four_intersecting_and_card_submultisetPartitionEquiv M hpos hle
    rw [Nat.card_congr e]
  · have hlt : n < M.sum := by omega
    have h_empty : IsEmpty {p : Nat.Partition n // M ≤ p.parts} := by
      constructor
      intro ⟨p, hp⟩
      have hsum := unrestricted_partition_family_four_intersecting_and_card_multiset_sum_le_sum_of_le hp
      have hp_sum := p.parts_sum
      omega
    have : Nat.card {p : Nat.Partition n // M ≤ p.parts} = 0 := Nat.card_eq_zero.mpr (Or.inl h_empty)
    rw [this, Nat.cast_zero]

lemma unrestricted_partition_family_four_intersecting_and_card_sum_if_submultiset_eq (n : ℕ) (M : Multiset ℕ) (hpos : ∀ x ∈ M, 0 < x) :
    (∑ p : Nat.Partition n, (if M ≤ p.parts then (1 : ℤ) else 0)) = partition_number (n - (M.sum : ℤ)) := by
  have h1 : (∑ p : Nat.Partition n, (if M ≤ p.parts then (1 : ℤ) else 0)) = (Nat.card {p : Nat.Partition n // M ≤ p.parts} : ℤ) := by
    rw [← Finset.sum_filter]
    simp only [sum_const, nsmul_eq_mul, mul_one]
    congr 1
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [h1, unrestricted_partition_family_four_intersecting_and_card_card_partition_containing_multiset n M hpos]

lemma unrestricted_partition_family_four_intersecting_and_card_mem_and_mem_iff_le_two {a b : ℕ} (hab : a ≠ b) (s : Multiset ℕ) :
    (a ∈ s ∧ b ∈ s) ↔ (a ::ₘ b ::ₘ 0) ≤ s := by
  have h1 : a ∉ (b ::ₘ 0 : Multiset ℕ) := by simp [hab]
  have h2 : b ∉ (0 : Multiset ℕ) := by simp
  rw [cons_le_of_notMem h1, cons_le_of_notMem h2]
  simp [and_comm]

lemma unrestricted_partition_family_four_intersecting_and_card_mem_and_mem_and_mem_iff_le_three {a b c : ℕ} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (s : Multiset ℕ) :
    (a ∈ s ∧ b ∈ s ∧ c ∈ s) ↔ (a ::ₘ b ::ₘ c ::ₘ 0) ≤ s := by
  have h1 : a ∉ (b ::ₘ c ::ₘ 0 : Multiset ℕ) := by simp [hab, hac]
  have h2 : b ∉ (c ::ₘ 0 : Multiset ℕ) := by simp [hbc]
  have h3 : c ∉ (0 : Multiset ℕ) := by simp
  rw [cons_le_of_notMem h1, cons_le_of_notMem h2, cons_le_of_notMem h3]
  simp

lemma unrestricted_partition_family_four_intersecting_and_card_hpos_two {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : ∀ x ∈ (a ::ₘ b ::ₘ 0 : Multiset ℕ), 0 < x := by
  intro x hx
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
  rcases hx with rfl | rfl <;> assumption

lemma unrestricted_partition_family_four_intersecting_and_card_hpos_three {a b c : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    ∀ x ∈ (a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℕ), 0 < x := by
  intro x hx
  simp only [Multiset.mem_cons, Multiset.notMem_zero, or_false] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

lemma unrestricted_partition_family_four_intersecting_and_card_sum_b2z_two (n : ℕ) (a b : ℕ) (hab : a ≠ b) (ha : 0 < a) (hb : 0 < b) :
    (∑ p : Nat.Partition n, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (a ∈ p.parts) && decide (b ∈ p.parts))) =
      partition_number (n - ((a ::ₘ b ::ₘ 0 : Multiset ℕ).sum : ℤ)) := by
  have h : ∀ p : Nat.Partition n, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (a ∈ p.parts) && decide (b ∈ p.parts)) =
      if (a ::ₘ b ::ₘ 0) ≤ p.parts then (1 : ℤ) else 0 := by
    intro p
    simp only [unrestricted_partition_family_four_intersecting_and_card_b2z]
    apply if_congr _ rfl rfl
    rw [Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff]
    exact unrestricted_partition_family_four_intersecting_and_card_mem_and_mem_iff_le_two hab p.parts
  simp_rw [h]
  exact unrestricted_partition_family_four_intersecting_and_card_sum_if_submultiset_eq n (a ::ₘ b ::ₘ 0) (unrestricted_partition_family_four_intersecting_and_card_hpos_two ha hb)

lemma unrestricted_partition_family_four_intersecting_and_card_sum_b2z_three (n : ℕ) (a b c : ℕ) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    (∑ p : Nat.Partition n, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (a ∈ p.parts) && decide (b ∈ p.parts) && decide (c ∈ p.parts))) =
      partition_number (n - ((a ::ₘ b ::ₘ c ::ₘ 0 : Multiset ℕ).sum : ℤ)) := by
  have h : ∀ p : Nat.Partition n, unrestricted_partition_family_four_intersecting_and_card_b2z (decide (a ∈ p.parts) && decide (b ∈ p.parts) && decide (c ∈ p.parts)) =
      if (a ::ₘ b ::ₘ c ::ₘ 0) ≤ p.parts then (1 : ℤ) else 0 := by
    intro p
    simp only [unrestricted_partition_family_four_intersecting_and_card_b2z]
    apply if_congr _ rfl rfl
    simp only [Bool.and_eq_true, decide_eq_true_iff, and_assoc]
    exact unrestricted_partition_family_four_intersecting_and_card_mem_and_mem_and_mem_iff_le_three hab hac hbc p.parts
  simp_rw [h]
  exact unrestricted_partition_family_four_intersecting_and_card_sum_if_submultiset_eq n (a ::ₘ b ::ₘ c ::ₘ 0) (unrestricted_partition_family_four_intersecting_and_card_hpos_three ha hb hc)

/-- Proposition 6.1 (arXiv:2610.01747): A_n is 1-intersecting and its cardinality satisfies the alternating sum formula in terms of p(n-k). -/
theorem unrestricted_partition_family_four_intersecting_and_card (n : ℕ) (hn : 1 ≤ n) :
    is_t_intersecting_partition_family 1 (partition_A n) ∧
    ((partition_A n).card : ℤ) =
      partition_number (n - 3 : ℤ) + partition_number (n - 4 : ℤ) + partition_number (n - 5 : ℤ) -
      partition_number (n - 6 : ℤ) - partition_number (n - 7 : ℤ) - partition_number (n - 8 : ℤ) +
      partition_number (n - 9 : ℤ) := by
  refine ⟨partition_A_is_one_intersecting n, ?_⟩
  have h_card := (unrestricted_partition_family_four_intersecting_and_card_sum_b2z_decide_mem n (partition_A n)).symm
  rw [h_card]
  have h_eq : ∀ p : Nat.Partition n,
      unrestricted_partition_family_four_intersecting_and_card_b2z (decide (p ∈ partition_A n)) =
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (2 ∈ p.parts)) +
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (3 ∈ p.parts)) +
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (4 ∈ p.parts)) -
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (2 ∈ p.parts) && decide (3 ∈ p.parts)) -
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (2 ∈ p.parts) && decide (4 ∈ p.parts)) -
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (1 ∈ p.parts) && decide (3 ∈ p.parts) && decide (4 ∈ p.parts)) +
        unrestricted_partition_family_four_intersecting_and_card_b2z (decide (2 ∈ p.parts) && decide (3 ∈ p.parts) && decide (4 ∈ p.parts)) := by
    intro p
    rw [unrestricted_partition_family_four_intersecting_and_card_decide_mem_partition_A]
    exact unrestricted_partition_family_four_intersecting_and_card_bool_pie _ _ _ _
  simp_rw [h_eq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have s12 : ((1 ::ₘ 2 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 3 := by rfl
  have s13 : ((1 ::ₘ 3 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 4 := by rfl
  have s14 : ((1 ::ₘ 4 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 5 := by rfl
  have s123 : ((1 ::ₘ 2 ::ₘ 3 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 6 := by rfl
  have s124 : ((1 ::ₘ 2 ::ₘ 4 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 7 := by rfl
  have s134 : ((1 ::ₘ 3 ::ₘ 4 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 8 := by rfl
  have s234 : ((2 ::ₘ 3 ::ₘ 4 ::ₘ 0 : Multiset ℕ).sum : ℤ) = 9 := by rfl
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_two n 1 2 (by decide) (by decide) (by decide), s12]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_two n 1 3 (by decide) (by decide) (by decide), s13]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_two n 1 4 (by decide) (by decide) (by decide), s14]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_three n 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s123]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_three n 1 2 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s124]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_three n 1 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s134]
  rw [unrestricted_partition_family_four_intersecting_and_card_sum_b2z_three n 2 3 4 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide), s234]
