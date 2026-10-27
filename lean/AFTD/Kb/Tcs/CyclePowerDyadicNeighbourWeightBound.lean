import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerDyadicPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicPairCountPrune
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCountPruneLow
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCountPruneTop
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCountTopBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_neighbour_weight_bound

Topic: combinatorics   Node: 4cf3f135f8dc

Provenance: helper lemma. Proposed uniform induction lemma for OP-205 / RT-1, arXiv:2610.15635. Closed-form weights were recovered from experiments6432,6434,6435 and an explicit pruning induction is recorded. The statement remains unproved until Lean checks that induction; no advance is claimed.

A tight rooted dyadic class satisfies a uniform weighted bound for the ordinary distances one below the dyadic long distances, with a penalty supported only at the two central positions.
-/

open Finset

lemma cycle_power_dyadic_neighbour_weight_bound_aux
    (k : ℕ) (b : ℕ → Bool)
    (hroot : b 0 = true ∧ b (2 ^ (k+2) - 1) = true)
    (htight : cycle_power_dyadic_class_weight (k+2) b =
      (range (2 ^ (k+2))).sum (fun a => (b a).toNat)) :
    (range (k+2)).sum (fun j => if 1 ≤ j then
      2^j * cycle_power_dyadic_neighbour_pair_count (k+2) j b else 0) ≤
    cycle_power_dyadic_pair_count (k+2) 1 b +
      (range (k+2)).sum (fun j => if 2 ≤ j then
        2^j * cycle_power_dyadic_pair_count (k+2) j b else 0) +
      2^(k+1) * ((b (2^(k+1)-1)).toNat + (b (2^(k+1))).toNat) := by
  induction k generalizing b with
  | zero =>
    norm_num only [Nat.reduceAdd, Nat.reducePow, Nat.reduceSub] at hroot ⊢
    simp only [cycle_power_dyadic_pair_count, cycle_power_dyadic_neighbour_pair_count,
      sum_range_succ, sum_range_zero, Nat.reduceAdd, Nat.reducePow,
      Nat.reduceSub, Nat.le_refl, Nat.reduceLeDiff, ↓reduceIte,
      Nat.zero_le, Nat.not_succ_le_zero, add_zero, zero_add,
      hroot.1, hroot.2, Bool.true_and, Bool.and_true]
    cases b 1 <;> cases b 2 <;> decide
  | succ k ih =>
    let q := 2^(k+1)
    let bb := cycle_power_dyadic_b_lift (k+1) b
    have hq : 0 < q := Nat.two_pow_pos (k+1)
    have hH : 2^(k+2)=2*q := by dsimp [q]; rw [show k+2=(k+1)+1 by omega, pow_succ]; omega
    have hD : 2^(k+3)=4*q := by rw [show k+3=(k+2)+1 by omega, pow_succ, hH]; omega
    have hD' : 2^(k+1+2)=4*q := hD
    have hbroot : bb 0 = true ∧ bb (2^(k+2)-1) = true := by
      constructor
      · dsimp [bb, cycle_power_dyadic_b_lift]; rw [if_pos hq]; exact hroot.1
      · dsimp [bb, cycle_power_dyadic_b_lift]
        rw [if_neg (by omega)]
        have he : 2^(k+2)-1+2^(k+2)=2^(k+1+2)-1 := by omega
        rw [he]; exact hroot.2
    have hbtight := cycle_power_dyadic_tight_class_prune (k+1) b htight
    have hi := ih bb hbroot hbtight
    have hrel := cycle_power_dyadic_neighbour_pair_count_prune_top (k+1) b hroot
    have htop := cycle_power_dyadic_neighbour_pair_count_top_bound (k+1) b hroot htight
    have hsmallM :
        (range (k+1)).sum (fun j => if 1 ≤ j then
          2^j * cycle_power_dyadic_neighbour_pair_count (k+1+2) j b else 0) =
        (range (k+1)).sum (fun j => if 1 ≤ j then
          2^j * cycle_power_dyadic_neighbour_pair_count (k+2) j bb else 0) := by
      apply sum_congr rfl
      intro j hj
      rw [cycle_power_dyadic_neighbour_pair_count_prune_low (k+1) j (mem_range.mp hj)]
    have hsumM :
        (range (k+2)).sum (fun j => if 1 ≤ j then
          2^j * cycle_power_dyadic_neighbour_pair_count (k+1+2) j b else 0) +
            q*((b (q-1)).toNat+(b (3*q)).toNat) =
        (range (k+2)).sum (fun j => if 1 ≤ j then
          2^j * cycle_power_dyadic_neighbour_pair_count (k+2) j bb else 0) +
            q*((b (3*q-1)).toNat+(b q).toNat) := by
      have hs (f : ℕ → ℕ) : (range (k+2)).sum f =
          (range (k+1)).sum f + f (k+1) := sum_range_succ f (k+1)
      rw [hs, hsmallM, hs]
      simp only [show 1 ≤ k+1 by omega, ↓reduceIte]
      have hh := congrArg (fun v : ℕ => q*v) hrel
      dsimp only [q, bb] at hh ⊢
      nlinarith only [hh]
    have hsumN :
        (range (k+2)).sum (fun j => if 2 ≤ j then
          2^j * cycle_power_dyadic_pair_count (k+1+2) j b else 0) =
        (range (k+2)).sum (fun j => if 2 ≤ j then
          2^j * cycle_power_dyadic_pair_count (k+2) j bb else 0) := by
      apply sum_congr rfl
      intro j hj
      rw [cycle_power_dyadic_pair_count_prune (k+1) j (by have := mem_range.mp hj; omega)]
    have hN1 := cycle_power_dyadic_pair_count_prune (k+1) 1 (by omega) b
    have hcent : (bb (2^(k+1)-1)).toNat + (bb (2^(k+1))).toNat =
        (b (q-1)).toNat+(b (3*q)).toNat := by
      dsimp [bb, cycle_power_dyadic_b_lift]
      rw [if_pos (show 2^(k+1)-1 < 2^(k+1) by have := Nat.two_pow_pos (k+1); omega),
        if_neg (Nat.lt_irrefl (2^(k+1)))]
      have he : 2^(k+1)+2^(k+2)=3*q := by
        change q+2^(k+2)=3*q
        rw [hH]; omega
      rw [he]
    rw [hcent] at hi
    have hscaled := Nat.mul_le_mul_left q htop
    have hs (f : ℕ → ℕ) : (range (k+1+2)).sum f =
        (range (k+2)).sum f + f (k+2) := sum_range_succ f (k+2)
    rw [hs, hs]
    simp only [show 1 ≤ k+2 by omega, show 2 ≤ k+2 by omega, ↓reduceIte]
    rw [hsumN, hN1]
    have hpow : 2^(k+1+1)=2*q := hH
    rw [hH]
    change _ ≤ _ + _ + (2*q)*((b (2*q-1)).toNat+(b (2*q)).toNat)
    rw [hpow] at hscaled
    dsimp only [bb, q] at hi hsumM hscaled ⊢
    nlinarith only [hi, hsumM, hscaled]

theorem cycle_power_dyadic_neighbour_weight_bound
    (m : ℕ) (hm : 2 ≤ m) (b : ℕ → Bool)
    (hroot : b 0 = true ∧ b (2 ^ m - 1) = true)
    (htight : cycle_power_dyadic_class_weight m b =
      (Finset.range (2 ^ m)).sum (fun a => (b a).toNat)) :
    let D : ℕ := 2 ^ m
    let N : ℕ → ℕ := fun j => (Finset.range (2 ^ j)).sum
      (fun a => (b a && b (a + D - 2 ^ j)).toNat)
    let M : ℕ → ℕ := fun j => (Finset.range (2 ^ j + 1)).sum
      (fun a => (b a && b (a + D - 2 ^ j - 1)).toNat)
    (Finset.range m).sum (fun j => if 1 ≤ j then 2 ^ j * M j else 0) ≤
      N 1 + (Finset.range m).sum (fun j => if 2 ≤ j then 2 ^ j * N j else 0) +
        2 ^ (m - 1) * ((b (2 ^ (m - 1) - 1)).toNat + (b (2 ^ (m - 1))).toNat) := by
  obtain ⟨k, rfl⟩ : ∃ k, m=k+2 := ⟨m-2, by omega⟩
  exact cycle_power_dyadic_neighbour_weight_bound_aux k b hroot htight
