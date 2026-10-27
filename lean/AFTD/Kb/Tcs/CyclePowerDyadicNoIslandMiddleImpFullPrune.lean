import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_middle_imp_full_prune

Topic: combinatorics   Node: b3564de501a2

Provenance: helper lemma. Conditional structural helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The no-island hypothesis remains explicit and unproved for the general periodic model. These helpers do not settle the covering-number conjecture, and no research advance is claimed.

If a tight dyadic two-interval class contains any middle-quarter vertex, deleting the middle two quarters leaves a full smaller class. Interval widths may be unequal and exceed half the original radius.
-/

open Finset

theorem cycle_power_dyadic_no_island_middle_imp_full_prune
    (k : ℕ) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight (k+2) b =
      (range (2^(k+2))).sum (fun a => (b a).toNat))
    (hshape : ∀ (a c d : ℕ), a < c → c < d → d < 2^(k+2) →
      b a = false → b c = true → b d = true)
    (a : ℕ) (ha0 : 2^k ≤ a) (ha1 : a < 3*2^k) (hba : b a = true) :
    ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k b i = true := by
  let q := 2^k
  have hq : 0 < q := Nat.two_pow_pos _
  have hH : 2^(k+1)=2*q := by dsimp [q]; rw [pow_succ]; omega
  have hD : 2^(k+2)=4*q := by rw [show k+2=(k+1)+1 by omega, pow_succ,hH]; omega
  have hp := cycle_power_dyadic_tight_class_middle_parent k b htight
  have hparentL (i : ℕ) (hi0 : q ≤ i) (hi1 : i < 2*q) :
      b i = true → b (i+2*q) = true := by
    simpa only [hH] using hp.1 i hi0 (by omega)
  have hparentR (i : ℕ) (hi0 : 2*q ≤ i) (hi1 : i < 3*q) :
      b i = true → b (i-2*q) = true := by
    simpa only [hH] using hp.2 i (by omega) hi1
  have hleft (c : ℕ) (hc : c < q) : b c = true := by
    by_contra hcne
    have hcf : b c = false := Bool.eq_false_iff.mpr hcne
    have hu : b (3*q-1) = true := by
      by_cases he : a=3*q-1
      · rw [← he]; exact hba
      exact hshape c a (3*q-1) (by omega) (by omega) (by omega) hcf hba
    have huq := hparentR (3*q-1) (by omega) (by omega) hu
    have hi : 3*q-1-2*q=q-1 := by omega
    rw [hi] at huq
    by_cases he : c=q-1
    · rw [he,huq] at hcf
      contradiction
    have hmid : b (2*q+c) = true :=
      hshape c (q-1) (2*q+c) (by omega) (by omega) (by omega) hcf huq
    have hh := hparentR (2*q+c) (by omega) (by omega) hmid
    have heq : 2*q+c-2*q=c := by omega
    rw [heq,hcf] at hh
    contradiction
  have hright (c : ℕ) (hc0 : 3*q ≤ c) (hc1 : c < 4*q) : b c = true := by
    by_contra hcne
    have hcf : b c = false := Bool.eq_false_iff.mpr hcne
    have hbq : b q = true := by
      by_cases he : a=q
      · rw [← he]; exact hba
      by_contra hqne
      have hqf : b q = false := Bool.eq_false_iff.mpr hqne
      have hh := hshape q a c (by omega) (by omega) (by omega) hqf hba
      rw [hcf] at hh
      contradiction
    have hu := hparentL q (by omega) (by omega) hbq
    have hi : q+2*q=3*q := by omega
    rw [hi] at hu
    by_cases he : c=3*q
    · rw [he,hu] at hcf
      contradiction
    have hbi : b (c-2*q) = true := by
      by_contra hine
      have hif : b (c-2*q) = false := Bool.eq_false_iff.mpr hine
      have hh := hshape (c-2*q) (3*q) c (by omega) (by omega) (by omega) hif hu
      rw [hcf] at hh
      contradiction
    have hh := hparentL (c-2*q) (by omega) (by omega) hbi
    have heq : c-2*q+2*q=c := by omega
    rw [heq,hcf] at hh
    contradiction
  intro i hi
  dsimp [cycle_power_dyadic_b_lift]
  by_cases hil : i < 2^k
  · rw [if_pos hil]
    exact hleft i hil
  · rw [if_neg hil]
    exact hright (i+2^(k+1)) (by omega) (by omega)
