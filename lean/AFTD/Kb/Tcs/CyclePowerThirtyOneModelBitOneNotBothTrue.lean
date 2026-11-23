import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28tM2b28t
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28tM2b28f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28fM6t4t
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28fM6t4f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28fM6fM2t
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleTrueBitOneRefuted3b28fM6fM2f

/-!
# cycle_power_thirty_one_model_bit_one_not_both_true

Topic: combinatorics   Node: 346dab177c5d

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case.

In a tight, exactly dyadically covered, fully covered exponent-5 model with 6 active classes per vertex, no two consecutive classes both contain bit 1: x(p,1) = true implies x(p+1,1) = false.
-/

-- uses RT1C32.model_shift from the s5f module

theorem cycle_power_thirty_one_model_bit_one_not_both_true (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1) :
    ∀ p : ℤ, x p 1 = true → x (p+1) 1 = false := by
  have key : ∀ y : ℤ → ℕ → Bool,
      (∀ p, cycle_power_dyadic_class_weight (4+1) (y p) =
        (Finset.range (2^(4+1))).sum (fun a => (y p a).toNat)) →
      (∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ y (v-(a : ℤ)) a = true ∧
          y (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (y (v-(a : ℤ)) a).toNat) = (4+1)+1) →
      y (0 : ℤ) 1 = true → y (1 : ℤ) 1 = true → False := by
    intro y htight hexact hcover hcount hu0 hu1
    by_cases h0 : y (3 : ℤ) 28 = true
    · by_cases h1 : y (-2 : ℤ) 28 = true
      · exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28t_m2b28t y htight hexact hcover hcount hu0 hu1 h0 h1
      · have h1 : y (-2 : ℤ) 28 = false := by simpa using h1
        exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28t_m2b28f y htight hexact hcover hcount hu0 hu1 h0 h1
    · have h0 : y (3 : ℤ) 28 = false := by simpa using h0
      by_cases h1 : y (-6 : ℤ) 1 = true
      · by_cases h2 : y (4 : ℤ) 1 = true
        · exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28f_m6t_4t y htight hexact hcover hcount hu0 hu1 h0 h1 h2
        · have h2 : y (4 : ℤ) 1 = false := by simpa using h2
          exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28f_m6t_4f y htight hexact hcover hcount hu0 hu1 h0 h1 h2
      · have h1 : y (-6 : ℤ) 1 = false := by simpa using h1
        by_cases h2 : y (-2 : ℤ) 1 = true
        · exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28f_m6f_m2t y htight hexact hcover hcount hu0 hu1 h0 h1 h2
        · have h2 : y (-2 : ℤ) 1 = false := by simpa using h2
          exact cycle_power_thirty_one_double_true_bit_one_refuted_3b28f_m6f_m2f y htight hexact hcover hcount hu0 hu1 h0 h1 h2
  intro p hp
  by_contra hq
  have hq' : x (p+1) 1 = true := by simpa using hq
  obtain ⟨t, e, c, n⟩ := RT1C32.model_shift x ⟨htight, hexact, hcover, hcount⟩ p
  exact key (fun q a => x (p+q) a) t e c n (by simpa using hp) (by simpa using hq')
