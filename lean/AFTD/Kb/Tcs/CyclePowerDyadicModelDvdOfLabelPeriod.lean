import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicCentralPositionExists
import AFTD.Kb.Tcs.PeriodicDyadicDvdOfHalfShiftNe
import AFTD.Kb.Tcs.CyclePowerClassHalfShiftNeOfCentralOccurrence
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_model_dvd_of_label_period

Topic: combinatorics   Node: c49738e5bea4

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

A finite-period tight dyadic class model with proper labels, exact dyadic edges, neighbour coverage, and full-radius label period has model period divisible by the radius. Full-radius label periodicity remains an explicit hypothesis; optimal scalar counts and shape periods are unnecessary.
-/

open Finset

theorem cycle_power_dyadic_model_dvd_of_label_period
    (m n : ℕ) (hm : 2 ≤ m) (hn : 0 < n)
    (x : ℤ → ℕ → Bool) (ell : ℤ → Fin (m+1))
    (hperiod : ∀ p a, x (p+(n : ℤ)) a = x p a)
    (hell : ∀ p, ell (p+(n : ℤ)) = ell p)
    (hlabel : ∀ p, ell (p+((2^m : ℕ) : ℤ)) = ell p)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^j+1 ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+2^m-2^j-1) = true)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < 2^m → b < 2^m → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ))) :
    2^m ∣ n := by
  have hpow : 2^m=2*2^(m-1) := by
    conv_lhs => rw [show m=(m-1)+1 by omega]
    rw [pow_succ]; omega
  have hroot (p : ℤ) : x p 0 = true ∧ x p (2*2^(m-1)-1) = true := by
    have hh := hexact 0 (by omega) p
    norm_num only [pow_zero, sum_range_one, Nat.cast_zero, sub_zero,
      Nat.zero_add] at hh
    rw [← hpow]
    cases h0 : x p 0 <;> cases h1 : x p (2^m-1) <;> simp_all
  have hc := cycle_power_dyadic_central_position_exists m n hm hn x hperiod htight hexact hcover
  have hs := cycle_power_class_half_shift_ne_of_central_occurrence (2^(m-1))
    (Nat.two_pow_pos _) x ell hroot (by simpa only [← hpow] using hsep) hc
  have hdy : Function.Periodic ell ((2^(m-1+1) : ℕ) : ℤ) := by
    rw [Nat.sub_add_cancel (show 1 ≤ m by omega)]
    exact hlabel
  have hd := periodic_dyadic_dvd_of_half_shift_ne (m-1) n ell hell hdy hs
  simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega)] using hd
