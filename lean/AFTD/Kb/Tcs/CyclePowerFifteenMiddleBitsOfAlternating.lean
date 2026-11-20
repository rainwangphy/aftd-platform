import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicMiddleBitsFromDefectiveHalves
import AFTD.Kb.Tcs.CyclePowerEightDefectiveHalvesNoDefects
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_fifteen_middle_bits_of_alternating

Topic: combinatorics   Node: c6644c8eb56a

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the t = 3 (bandwidth 15) case of cycle_power_dyadic_middle_bits_of_alternating.

In a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent 4 (offsets 0..15) with 5 active classes per vertex, where bit 1 alternates and every class without bit 1 has no inner bits other than possibly 7 and 8, those two middle bits vanish too: every class without bit 1 consists of its endpoints only.
-/

theorem cycle_power_fifteen_middle_bits_of_alternating (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (3+1) (x p) =
      (Finset.range (2^(3+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 3+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(3+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(3+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(3+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(3+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (3+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hpart : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(3+1) - 1 → j ≠ 2^3 - 1 → j ≠ 2^3 →
      x p j = false) :
    ∀ p : ℤ, x p 1 = false → x p (2^3 - 1) = false ∧ x p (2^3) = false := by
  exact cycle_power_dyadic_middle_bits_from_defective_halves 3 (by norm_num) x htight hexact hcover
    hcount halt hpart cycle_power_eight_defective_halves_no_defects
