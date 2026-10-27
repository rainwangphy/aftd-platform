import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicNeighbourPairCount
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_neighbour_pair_count_top_bound

Topic: combinatorics   Node: 7b6456a93ba1

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

The largest neighbour pair count of a tight rooted class is controlled by its middle-quarter leaves and the two central bits.
-/

open Finset

theorem cycle_power_dyadic_neighbour_pair_count_top_bound
    (k : ℕ) (b : ℕ → Bool)
    (hroot : b 0 = true ∧ b (2 ^ (k + 2) - 1) = true)
    (htight : cycle_power_dyadic_class_weight (k + 2) b =
      (range (2 ^ (k + 2))).sum (fun a => (b a).toNat)) :
    2 * cycle_power_dyadic_neighbour_pair_count (k + 2) (k + 1) b +
        (b (3 * 2 ^ k - 1)).toNat + (b (2 ^ k)).toNat ≤
      2 * cycle_power_dyadic_pair_count (k + 2) (k + 1) b +
        2 * ((b (2 ^ (k + 1) - 1)).toNat + (b (2 ^ (k + 1))).toNat) := by
  let q := 2 ^ k
  have hq : 0 < q := Nat.two_pow_pos k
  have hH : 2 ^ (k + 1) = 2 * q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2 ^ (k + 2) = 4 * q := by rw [show k+2=(k+1)+1 by omega, pow_succ, hH]; omega
  have hr0 : b 0 = true := hroot.1
  have hr1 : b (4 * q - 1) = true := by simpa only [hD] using hroot.2
  have hp := cycle_power_dyadic_tight_class_middle_parent k b htight
  have hsfirst (f : ℕ → ℕ) : (range q).sum f =
      f 0 + (range (q-1)).sum (fun a => f (a+1)) := by
    rw [show range q = range ((q-1)+1) by congr 1; omega, sum_range_succ']
    omega
  have hslast (f : ℕ → ℕ) : (range q).sum f =
      (range (q-1)).sum f + f (q-1) := by
    rw [show range q = range ((q-1)+1) by congr 1; omega, sum_range_succ]
  have hNL (a : ℕ) (ha : a < q) :
      (b a && b (a + 2 * q)).toNat = (b (a + 2 * q)).toNat := by
    have hh : b (a+2*q) = true → b a = true := by
      have hh := hp.2 (a+2*q) (by omega) (by omega)
      simpa only [hH, Nat.add_sub_cancel_right] using hh
    cases hba : b a <;> cases hbb : b (a+2*q) <;> simp_all
  have hNR (a : ℕ) (ha : a < q) :
      (b (q+a) && b (q+a+2*q)).toNat = (b (q+a)).toNat := by
    have hh : b (q+a) = true → b (q+a+2*q) = true := by
      simpa only [hH] using hp.1 (q+a) (by omega) (by omega)
    cases hba : b (q+a) <;> cases hbb : b (q+a+2*q) <;> simp_all
  have hN : cycle_power_dyadic_pair_count (k+2) (k+1) b =
      (range (q-1)).sum (fun a => (b (a+2*q)).toNat) +
        (b (3*q-1)).toNat + (b q).toNat +
        (range (q-1)).sum (fun a => (b (q+a+1)).toNat) := by
    unfold cycle_power_dyadic_pair_count
    rw [hH, hD, show range (2*q)=range (q+q) by congr 1; omega, sum_range_add]
    have hl : (range q).sum (fun a => (b a && b (a+4*q-2*q)).toNat) =
        (range q).sum (fun a => (b (a+2*q)).toNat) := by
      apply sum_congr rfl
      intro a ha
      have he : a+4*q-2*q=a+2*q := by omega
      rw [he]; exact hNL a (mem_range.mp ha)
    have hr : (range q).sum (fun a => (b (q+a) && b (q+a+4*q-2*q)).toNat) =
        (range q).sum (fun a => (b (q+a)).toNat) := by
      apply sum_congr rfl
      intro a ha
      have he : q+a+4*q-2*q=q+a+2*q := by omega
      rw [he]; exact hNR a (mem_range.mp ha)
    rw [hl, hr]
    rw [hslast, hsfirst]
    have he : q-1+2*q=3*q-1 := by omega
    simp only [he, Nat.add_zero]
    have heq : (fun a => (b (q+(a+1))).toNat) = (fun a => (b (q+a+1)).toNat) := by
      funext a; congr 2 <;> omega
    rw [heq]; omega
  have hML : (range (q-1)).sum
      (fun a => (b (a+1) && b (a+2*q)).toNat) ≤
        (range (q-1)).sum (fun a => (b (a+2*q)).toNat) := by
    exact sum_le_sum (fun a _ => cycle_power_dyadic_bool_and_toNat_le_right _ _)
  have hMR : (range (q-1)).sum
      (fun a => (b (q+a+1) && b (3*q+a)).toNat) ≤
        (range (q-1)).sum (fun a => (b (q+a+1)).toNat) := by
    exact sum_le_sum (fun a _ => cycle_power_dyadic_bool_and_toNat_le_left _ _)
  have hM : cycle_power_dyadic_neighbour_pair_count (k+2) (k+1) b =
      (b (2*q-1)).toNat +
        (range (q-1)).sum (fun a => (b (a+1) && b (a+2*q)).toNat) +
        (b q && b (3*q-1)).toNat +
        (range (q-1)).sum (fun a => (b (q+a+1) && b (3*q+a)).toNat) +
        (b (2*q)).toNat := by
    unfold cycle_power_dyadic_neighbour_pair_count
    rw [hH, hD, sum_range_succ]
    have hlast : 2*q+4*q-2*q-1=4*q-1 := by omega
    rw [hlast, hr1, Bool.and_true]
    rw [show range (2*q)=range (q+q) by congr 1; omega, sum_range_add]
    have hl : (range q).sum (fun a => (b a && b (a+4*q-2*q-1)).toNat) =
        (b (2*q-1)).toNat +
          (range (q-1)).sum (fun a => (b (a+1) && b (a+2*q)).toNat) := by
      rw [hsfirst]
      simp only [Nat.zero_add, hr0, Bool.true_and]
      have he : 4*q-2*q-1=2*q-1 := by omega
      rw [he]
      congr 1
      apply sum_congr rfl
      intro a ha
      congr 2; congr 1; omega
    have hr : (range q).sum (fun a => (b (q+a) && b (q+a+4*q-2*q-1)).toNat) =
        (b q && b (3*q-1)).toNat +
          (range (q-1)).sum (fun a => (b (q+a+1) && b (3*q+a)).toNat) := by
      rw [hsfirst]
      simp only [Nat.add_zero]
      have he : q+4*q-2*q-1=3*q-1 := by omega
      rw [he]
      congr 1
      apply sum_congr rfl
      intro a ha
      congr 2 <;> congr 1 <;> omega
    rw [hl, hr]
    omega
  have hbits (a c : Bool) : 2 * (a && c).toNat ≤ a.toNat+c.toNat := by
    cases a <;> cases c <;> decide
  have hb := hbits (b q) (b (3*q-1))
  rw [hH]
  change 2 * cycle_power_dyadic_neighbour_pair_count (k+2) (k+1) b +
      (b (3*q-1)).toNat + (b q).toNat ≤ _
  omega
