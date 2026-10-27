import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourWeightBound
import AFTD.Kb.Tcs.ZmodSumSubEqSum
import AFTD.Kb.Tcs.CyclePowerDyadicPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCount
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cycle_power_dyadic_central_position_exists

Topic: combinatorics   Node: 1607538785a7

Provenance: helper lemma. Uniform consequence planned for the new neighbour-weight inequality in OP-205 / RT-1, arXiv:2610.15635. It remains unproved while its weight-bound dependency is unproved; no research advance or main solution claimed.

In a periodic tight dyadic class model with exact dyadic coverage and coverage at all lower neighbour distances, some class uses one of the two central positions. This requires neither a full class nor a preclassified class profile.
-/

open Finset

theorem cycle_power_dyadic_central_position_exists
    (m n : ℕ) (hm : 2 ≤ m) (hn : 0 < n) (x : ℤ → ℕ → Bool)
    (hperiod : ∀ p a, x (p + (n : ℤ)) a = x p a)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (Finset.range (2 ^ m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2 ^ j)).sum (fun a =>
      (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2 ^ j + 1 ∧ x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j - 1) = true) :
    ∃ p : ℤ, x p (2 ^ (m - 1) - 1) = true ∨ x p (2 ^ (m - 1)) = true := by
  classical
  by_contra hnone
  push_neg at hnone
  letI : NeZero n := ⟨by omega⟩
  let y : ZMod n → ℕ → Bool := fun p a => x (p.val : ℤ) a
  have hval (v : ℤ) (a : ℕ) : y (v : ZMod n) a = x v a := by
    obtain ⟨z, hz⟩ := (ZMod.intCast_eq_iff n v (v : ZMod n)).mp rfl
    have hp : Function.Periodic (fun p : ℤ => x p a) (n : ℤ) := fun p => hperiod p a
    have hh := hp.int_mul z (((v : ZMod n).val : ℤ))
    have he : ((v : ZMod n).val : ℤ)+z*(n : ℤ)=v := by
      calc
        _ = ((v : ZMod n).val : ℤ)+(n : ℤ)*z := by ring
        _ = v := hz.symm
    exact hh.symm.trans (congrArg (fun w : ℤ => x w a) he)
  have hshift (v : ZMod n) (a j : ℕ) :
      y (v-(a : ZMod n)) j = x ((v.val : ℤ)-(a : ℤ)) j := by
    have hh := hval ((v.val : ℤ)-(a : ℤ)) j
    simpa only [Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val] using hh
  have hroot (p : ZMod n) : y p 0 = true ∧ y p (2^m-1) = true := by
    have hh := hexact 0 (by omega) (p.val : ℤ)
    norm_num only [pow_zero, sum_range_one, Nat.cast_zero, sub_zero,
      Nat.zero_add] at hh
    dsimp [y]
    cases h0 : x (p.val : ℤ) 0 <;>
      cases h1 : x (p.val : ℤ) (2^m-1) <;> simp_all
  have hN (j : ℕ) (hj : j < m) :
      (∑ p : ZMod n, cycle_power_dyadic_pair_count m j (y p)) = n := by
    unfold cycle_power_dyadic_pair_count
    rw [sum_comm]
    calc
      _ = ∑ a ∈ range (2^j), ∑ v : ZMod n,
          (y (v-(a : ZMod n)) a && y (v-(a : ZMod n)) (a+2^m-2^j)).toNat := by
        apply sum_congr rfl
        intro a ha
        exact zmod_sum_sub_eq_sum n _ (a : ZMod n)
      _ = ∑ v : ZMod n, ∑ a ∈ range (2^j),
          (y (v-(a : ZMod n)) a && y (v-(a : ZMod n)) (a+2^m-2^j)).toNat := sum_comm
      _ = ∑ v : ZMod n, 1 := by
        apply sum_congr rfl
        intro v hv
        simp_rw [hshift]
        exact hexact j hj (v.val : ℤ)
      _ = n := by simp
  have hM (j : ℕ) (hj0 : 1 ≤ j) (hj : j < m) :
      n ≤ (∑ p : ZMod n, cycle_power_dyadic_neighbour_pair_count m j (y p)) := by
    unfold cycle_power_dyadic_neighbour_pair_count
    rw [sum_comm]
    have heq : (∑ a ∈ range (2^j+1), ∑ p : ZMod n,
          (y p a && y p (a+2^m-2^j-1)).toNat) =
        ∑ v : ZMod n, ∑ a ∈ range (2^j+1),
          (x ((v.val : ℤ)-(a : ℤ)) a &&
            x ((v.val : ℤ)-(a : ℤ)) (a+2^m-2^j-1)).toNat := by
      calc
        _ = ∑ a ∈ range (2^j+1), ∑ v : ZMod n,
            (y (v-(a : ZMod n)) a &&
              y (v-(a : ZMod n)) (a+2^m-2^j-1)).toNat := by
          apply sum_congr rfl
          intro a ha
          exact zmod_sum_sub_eq_sum n _ (a : ZMod n)
        _ = _ := by rw [sum_comm]; simp_rw [hshift]
    rw [heq]
    calc
      n = ∑ v : ZMod n, 1 := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro v hv
        obtain ⟨a, ha, ha0, ha1⟩ := hcover j hj0 hj (v.val : ℤ)
        have he := single_le_sum (fun (b : ℕ) _ => Nat.zero_le
          ((x ((v.val : ℤ)-(b : ℤ)) b &&
            x ((v.val : ℤ)-(b : ℤ)) (b+2^m-2^j-1)).toNat))
          (mem_range.mpr ha)
        simpa only [ha0, ha1, Bool.true_and, Bool.toNat_true] using he
  have hb (p : ZMod n) :
      (range m).sum (fun j => if 1 ≤ j then
        2^j * cycle_power_dyadic_neighbour_pair_count m j (y p) else 0) ≤
      cycle_power_dyadic_pair_count m 1 (y p) +
        (range m).sum (fun j => if 2 ≤ j then
          2^j * cycle_power_dyadic_pair_count m j (y p) else 0) := by
    have hh := cycle_power_dyadic_neighbour_weight_bound m hm (y p)
      (hroot p) (htight (p.val : ℤ))
    change _ ≤ _ + _ + _ at hh
    have h0 : y p (2^(m-1)-1) = false := by
      exact Bool.eq_false_iff.mpr (hnone (p.val : ℤ)).1
    have h1 : y p (2^(m-1)) = false := by
      exact Bool.eq_false_iff.mpr (hnone (p.val : ℤ)).2
    simpa only [cycle_power_dyadic_pair_count, cycle_power_dyadic_neighbour_pair_count,
      h0, h1, Bool.toNat_false, zero_add, mul_zero, add_zero] using hh
  let A := (range m).sum (fun j => if 1 ≤ j then 2^j else 0)
  let B := (range m).sum (fun j => if 2 ≤ j then 2^j else 0)
  have hAB : A = B+2 := by
    have he (j : ℕ) : (if 1 ≤ j then 2^j else 0) =
        (if 2 ≤ j then 2^j else 0) + (if j=1 then 2 else 0) := by
      by_cases h0 : j=0
      · subst j; decide
      by_cases h1 : j=1
      · subst j; decide
      simp [show 1 ≤ j by omega, show 2 ≤ j by omega, h1]
    dsimp [A, B]
    simp_rw [he, sum_add_distrib]
    simp [show 1 < m by omega]
  have hL : n*A ≤ ∑ p : ZMod n, (range m).sum (fun j => if 1 ≤ j then
      2^j * cycle_power_dyadic_neighbour_pair_count m j (y p) else 0) := by
    rw [sum_comm]
    calc
      n*A = (range m).sum (fun j => if 1 ≤ j then 2^j*n else 0) := by
        simp only [A, mul_sum, mul_ite, mul_zero]
        apply sum_congr rfl
        intro j hj
        split_ifs <;> ring
      _ ≤ _ := by
        apply sum_le_sum
        intro j hj
        by_cases hj0 : 1 ≤ j
        · simp only [hj0, ↓reduceIte, ← mul_sum]
          exact Nat.mul_le_mul_left (2^j) (hM j hj0 (mem_range.mp hj))
        · simp [hj0]
  have hR : (∑ p : ZMod n, (cycle_power_dyadic_pair_count m 1 (y p) +
        (range m).sum (fun j => if 2 ≤ j then
          2^j * cycle_power_dyadic_pair_count m j (y p) else 0))) = n+n*B := by
    rw [sum_add_distrib, hN 1 (by omega), sum_comm]
    congr 1
    calc
      _ = (range m).sum (fun j => if 2 ≤ j then 2^j*n else 0) := by
        apply sum_congr rfl
        intro j hj
        by_cases hj0 : 2 ≤ j
        · simp only [hj0, ↓reduceIte, ← mul_sum, hN j (mem_range.mp hj)]
        · simp [hj0]
      _ = n*B := by
        simp only [B, mul_sum, mul_ite, mul_zero]
        apply sum_congr rfl
        intro j hj
        split_ifs <;> ring
  have htot := sum_le_sum (s := (univ : Finset (ZMod n))) (fun p _ => hb p)
  rw [hR] at htot
  nlinarith only [hL, htot, hAB, hn]
