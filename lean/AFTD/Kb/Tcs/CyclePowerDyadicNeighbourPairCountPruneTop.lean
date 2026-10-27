import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_neighbour_pair_count_prune_top

Topic: combinatorics   Node: 05cdec8c1aa1

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

At the boundary rank of middle-quarter pruning, the neighbour pair count changes by exactly four boundary bits.
-/

open Finset

theorem cycle_power_dyadic_neighbour_pair_count_prune_top
    (k : ℕ) (b : ℕ → Bool) (hroot : b 0 = true ∧ b (2 ^ (k + 2) - 1) = true) :
    cycle_power_dyadic_neighbour_pair_count (k + 2) k b +
        (b (2 ^ k - 1)).toNat + (b (3 * 2 ^ k)).toNat =
      cycle_power_dyadic_neighbour_pair_count (k + 1) k (cycle_power_dyadic_b_lift k b) +
        (b (3 * 2 ^ k - 1)).toNat + (b (2 ^ k)).toNat := by
  let q := 2 ^ k
  have hq : 0 < q := Nat.two_pow_pos k
  have hH : 2 ^ (k + 1) = 2 * q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 4 * q := by rw [show k+2=(k+1)+1 by omega, pow_succ, hH]; omega
  have hr0 : b 0 = true := hroot.1
  have hr1 : b (4 * q - 1) = true := by simpa only [hD] using hroot.2
  have hsplit (f : ℕ → ℕ) :
      (range (q + 1)).sum f = f 0 + (range (q - 1)).sum (fun a => f (a+1)) + f q := by
    have hqr : q + 1 = (q - 1 + 1) + 1 := by omega
    rw [hqr, sum_range_succ, sum_range_succ']
    rw [show q-1+1=q by omega]
    omega
  have hb : ∀ a < q - 1,
      (cycle_power_dyadic_b_lift k b (a+1) &&
        cycle_power_dyadic_b_lift k b (a+1+2*q-q-1)).toNat =
      (b (a+1) && b (a+1+4*q-q-1)).toNat := by
    intro a ha
    dsimp [cycle_power_dyadic_b_lift]
    rw [if_pos (by dsimp [q] at *; omega), if_neg (by dsimp [q] at *; omega)]
    congr 2; congr 1; omega
  unfold cycle_power_dyadic_neighbour_pair_count
  rw [show 2^k=q from rfl, hD, hH, hsplit, hsplit]
  have hmid : (range (q-1)).sum (fun a =>
      (cycle_power_dyadic_b_lift k b (a+1) &&
        cycle_power_dyadic_b_lift k b (a+1+2*q-q-1)).toNat) =
      (range (q-1)).sum (fun a => (b (a+1) && b (a+1+4*q-q-1)).toNat) :=
    sum_congr rfl (fun a ha => hb a (mem_range.mp ha))
  rw [hmid]
  have hz : cycle_power_dyadic_b_lift k b 0 = b 0 := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_pos hq]
  have hqlo : cycle_power_dyadic_b_lift k b q = b (3*q) := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_neg (by omega)]
    congr 1; omega
  have hleft : cycle_power_dyadic_b_lift k b (0 + 2*q-q-1) = b (q-1) := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_pos (by omega)]
    congr 1; omega
  have hright : cycle_power_dyadic_b_lift k b (q + 2*q-q-1) = b (4*q-1) := by
    dsimp [cycle_power_dyadic_b_lift]; rw [if_neg (by omega)]
    congr 1; omega
  rw [hz, hqlo, hleft, hright, hr0, hr1]
  have he0 : 0 + 4*q-q-1=3*q-1 := by omega
  have he1 : q+4*q-q-1=4*q-1 := by omega
  rw [he0, he1, hr1]
  simp only [Bool.true_and, Bool.and_true]
  omega
