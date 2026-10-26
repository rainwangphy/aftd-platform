import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_class_weight_le

Topic: combinatorics   Node: 8309c31fc9a2

Provenance: helper lemma. Uniform route for OP-205 and RT-1, arXiv:2610.15635 Section 3. Existing k=3,7,15 weight certificates suggest this dyadic tree. The sparse distance graph is obtained recursively by attaching one leaf to every vertex; tight classes are connected subtrees containing the distinguished endpoint edge.

For every power-of-two arc length, the dyadic weighted number of selected pairs is at most the number of selected positions.
-/

open Finset

def cycle_power_dyadic_b_lift (k : ℕ) (b : ℕ → Bool) : ℕ → Bool :=
  fun x => if x < 2 ^ k then b x else b (x + 2 ^ (k + 1))

lemma cycle_power_dyadic_bool_and_toNat_le_left (x y : Bool) : (x && y).toNat ≤ x.toNat := by
  cases x <;> cases y <;> decide

lemma cycle_power_dyadic_bool_and_toNat_le_right (x y : Bool) : (x && y).toNat ≤ y.toNat := by
  cases x <;> cases y <;> decide

lemma cycle_power_dyadic_sum_range_four_blocks (L : ℕ) (f : ℕ → ℕ) :
    ∑ i ∈ range (4 * L), f i =
      (∑ i ∈ range L, f i) +
      (∑ i ∈ range L, f (L + i)) +
      (∑ i ∈ range L, f (2 * L + i)) +
      (∑ i ∈ range L, f (3 * L + i)) := by
  have h4 : 4 * L = L + (L + (L + L)) := by omega
  rw [h4]
  rw [sum_range_add, sum_range_add, sum_range_add]
  have h2 : (fun x => f (L + (L + x))) = (fun x => f (2 * L + x)) := by
    funext x; congr 1; omega
  have h3 : (fun x => f (L + (L + (L + x)))) = (fun x => f (3 * L + x)) := by
    funext x; congr 1; omega
  rw [h2, h3]
  omega

lemma cycle_power_dyadic_class_weight_succ (k : ℕ) (b : ℕ → Bool) :
    cycle_power_dyadic_class_weight (k + 2) b =
      cycle_power_dyadic_class_weight (k + 1) (cycle_power_dyadic_b_lift k b) +
        ∑ i ∈ range (2 ^ (k + 1)), (b i && b (i + 2 ^ (k + 1))).toNat := by
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ', mul_comm]
  have hk2 : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ', mul_comm]
  have hpos : 0 < 2 ^ k := Nat.two_pow_pos k
  have h_b0 : cycle_power_dyadic_b_lift k b 0 = b 0 := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_pos hpos]
  have h_last : cycle_power_dyadic_b_lift k b (2 ^ (k + 1) - 1) = b (2 ^ (k + 2) - 1) := by
    dsimp [cycle_power_dyadic_b_lift]
    have hge : 2 ^ k ≤ 2 ^ (k + 1) - 1 := by
      have : 1 ≤ 2 ^ k := Nat.one_le_two_pow; omega
    rw [if_neg (not_lt_of_ge hge)]
    congr 1
    have : 1 ≤ 2 ^ (k + 1) := Nat.one_le_two_pow; omega
  unfold cycle_power_dyadic_class_weight
  rw [sum_range_succ]
  have h_last_term : (if k + 1 = 0 then 0
      else ∑ i ∈ range (2 ^ (k + 1)), (b i && b (i + 2 ^ (k + 2) - 2 ^ (k + 1))).toNat) =
      ∑ i ∈ range (2 ^ (k + 1)), (b i && b (i + 2 ^ (k + 1))).toNat := by
    rw [if_neg (Nat.succ_ne_zero k)]
    congr 1
    ext i
    congr 2
    congr 1
    omega
  rw [h_last_term]
  have h_sum_eq :
      (∑ j ∈ range (k + 1), if j = 0 then 0 else ∑ i ∈ range (2 ^ j), (b i && b (i + 2 ^ (k + 2) - 2 ^ j)).toNat) =
      (∑ j ∈ range (k + 1), if j = 0 then 0 else ∑ i ∈ range (2 ^ j), (cycle_power_dyadic_b_lift k b i && cycle_power_dyadic_b_lift k b (i + 2 ^ (k + 1) - 2 ^ j)).toNat) := by
    apply sum_congr rfl
    intro j hj
    simp only [mem_range] at hj
    have hj_le : j ≤ k := Nat.lt_succ_iff.mp hj
    split_ifs with hj0
    · rfl
    · apply sum_congr rfl
      intro i hi
      simp only [mem_range] at hi
      have hi_lt : i < 2 ^ k := by
        have : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj_le
        exact lt_of_lt_of_le hi this
      have h1 : cycle_power_dyadic_b_lift k b i = b i := by
        dsimp [cycle_power_dyadic_b_lift]; rw [if_pos hi_lt]
      have hge : 2 ^ k ≤ i + 2 ^ (k + 1) - 2 ^ j := by
        have : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj_le
        omega
      have h2 : cycle_power_dyadic_b_lift k b (i + 2 ^ (k + 1) - 2 ^ j) = b (i + 2 ^ (k + 2) - 2 ^ j) := by
        dsimp [cycle_power_dyadic_b_lift]
        rw [if_neg (not_lt_of_ge hge)]
        congr 1
        have : 2 ^ j ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hj_le
        omega
      rw [h1, h2]
  rw [h_b0, h_last, h_sum_eq]
  omega

lemma cycle_power_dyadic_sum_lift_and_cross_le (k : ℕ) (b : ℕ → Bool) :
    (∑ i ∈ range (2 ^ (k + 1)), (cycle_power_dyadic_b_lift k b i).toNat) +
      (∑ i ∈ range (2 ^ (k + 1)), (b i && b (i + 2 ^ (k + 1))).toNat) ≤
    ∑ i ∈ range (2 ^ (k + 2)), (b i).toNat := by
  let L := 2 ^ k
  have hk1 : 2 ^ (k + 1) = L + L := by
    show 2 ^ (k + 1) = 2 ^ k + 2 ^ k
    rw [pow_succ', two_mul]
  have hk2 : 2 ^ (k + 2) = 4 * L := by
    show 2 ^ (k + 2) = 4 * 2 ^ k
    calc 2 ^ (k + 2) = 2 ^ k * 2 ^ 2 := pow_add 2 k 2
    _ = 2 ^ k * 4 := rfl
    _ = 4 * 2 ^ k := mul_comm _ _
  rw [hk1]
  rw [sum_range_add, sum_range_add]
  have h_lift1 : (∑ i ∈ range L, (cycle_power_dyadic_b_lift k b i).toNat) = ∑ i ∈ range L, (b i).toNat := by
    apply sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    dsimp [cycle_power_dyadic_b_lift, L] at *
    rw [if_pos hi]
  have h_lift2 : (∑ i ∈ range L, (cycle_power_dyadic_b_lift k b (L + i)).toNat) = ∑ i ∈ range L, (b (3 * L + i)).toNat := by
    apply sum_congr rfl
    intro i hi
    dsimp [cycle_power_dyadic_b_lift]
    have hge : 2 ^ k ≤ L + i := by dsimp [L]; omega
    rw [if_neg (not_lt_of_ge hge)]
    congr 2
    have : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ', mul_comm]
    dsimp [L]
    omega
  have h_cross1 : (∑ i ∈ range L, (b i && b (i + (L + L))).toNat) ≤ ∑ i ∈ range L, (b (2 * L + i)).toNat := by
    apply sum_le_sum
    intro i hi
    have : i + (L + L) = 2 * L + i := by omega
    rw [this]
    exact cycle_power_dyadic_bool_and_toNat_le_right (b i) (b (2 * L + i))
  have h_cross2 : (∑ i ∈ range L, (b (L + i) && b (L + i + (L + L))).toNat) ≤ ∑ i ∈ range L, (b (L + i)).toNat := by
    apply sum_le_sum
    intro i hi
    exact cycle_power_dyadic_bool_and_toNat_le_left (b (L + i)) (b (L + i + (L + L)))
  rw [h_lift1, h_lift2]
  rw [hk2]
  rw [cycle_power_dyadic_sum_range_four_blocks]
  omega

lemma cycle_power_dyadic_class_weight_le_aux (k : ℕ) (b : ℕ → Bool) :
    cycle_power_dyadic_class_weight (k + 1) b ≤
      (Finset.range (2 ^ (k + 1))).sum (fun i => (b i).toNat) := by
  induction k generalizing b with
  | zero =>
    unfold cycle_power_dyadic_class_weight
    rw [sum_range_one]
    simp only [ite_true, add_zero]
    norm_num
    rw [sum_range_succ, sum_range_one]
    cases b 0 <;> cases b 1 <;> decide
  | succ k ih =>
    rw [cycle_power_dyadic_class_weight_succ]
    exact le_trans (add_le_add_left (ih (cycle_power_dyadic_b_lift k b)) _) (cycle_power_dyadic_sum_lift_and_cross_le k b)

theorem cycle_power_dyadic_class_weight_le (m : ℕ) (hm : 1 ≤ m) (b : ℕ → Bool) :
    cycle_power_dyadic_class_weight m b ≤
      (Finset.range (2 ^ m)).sum (fun i => (b i).toNat) := by
  have h : m = (m - 1) + 1 := (Nat.sub_add_cancel hm).symm
  rw [h]
  exact cycle_power_dyadic_class_weight_le_aux (m - 1) b
