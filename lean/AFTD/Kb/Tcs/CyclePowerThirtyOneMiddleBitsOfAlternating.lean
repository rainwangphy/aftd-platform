import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicMiddleBitsFromDefectiveHalves
import AFTD.Kb.Tcs.CyclePowerSixteenDefectiveHalvesNoDefects

/-!
# cycle_power_thirty_one_middle_bits_of_alternating

Topic: combinatorics   Node: 8e7e7c6f5b75

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the t = 4 (bandwidth 31) case of cycle_power_dyadic_middle_bits_of_alternating.

The t = 4 case (k = 31) of cycle_power_dyadic_middle_bits_of_alternating: in a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent 5 with 6 active classes per vertex, with alternating bit 1 and with all inner bits other than 15 and 16 vanishing in the classes without bit 1, those two middle bits vanish there as well.
-/

theorem cycle_power_thirty_one_middle_bits_of_alternating (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
      (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (4+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(4+1) - 1 → j ≠ 2^4 - 1 → j ≠ 2^4 →
      x p j = false) :
    ∀ p : ℤ, x p 1 = false → x p (2^4 - 1) = false ∧ x p (2^4) = false := by
  exact cycle_power_dyadic_middle_bits_from_defective_halves 4 (by norm_num) x htight hexact hcover
    hcount halt hpart cycle_power_sixteen_defective_halves_no_defects
