import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5tM3f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5tM3t4t
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5tM3t4f28t
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5tM3t4f28f

/-!
# cycle_power_thirty_one_double_false_bit_one_refuted_s5t

Topic: combinatorics   Node: c806e84943cd

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case; one half of cycle_power_thirty_one_model_alternating (two consecutive classes without bit 1).

In a tight, exactly dyadically covered, fully covered exponent-5 model with 6 active classes per vertex, the classes rooted at 0 and 1 cannot both lack bit 1 when x(5,1) = true.
-/

-- the case split uses only the cube lemmas

theorem cycle_power_thirty_one_double_false_bit_one_refuted_s5t (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1)
    (hu0 : x (0 : ℤ) 1 = false) (hu1 : x (1 : ℤ) 1 = false) (hu2 : x (5 : ℤ) 1 = true) : False := by
  by_cases h0 : x (-3 : ℤ) 1 = true
  · by_cases h1 : x (4 : ℤ) 1 = true
    · exact cycle_power_thirty_one_double_false_bit_one_refuted_s5t_m3t_4t x htight hexact hcover hcount hu0 hu1 hu2 h0 h1
    · have h1 : x (4 : ℤ) 1 = false := by simpa using h1
      by_cases h2 : x (2 : ℤ) 28 = true
      · exact cycle_power_thirty_one_double_false_bit_one_refuted_s5t_m3t_4f_28t x htight hexact hcover hcount hu0 hu1 hu2 h0 h1 h2
      · have h2 : x (2 : ℤ) 28 = false := by simpa using h2
        exact cycle_power_thirty_one_double_false_bit_one_refuted_s5t_m3t_4f_28f x htight hexact hcover hcount hu0 hu1 hu2 h0 h1 h2
  · have h0 : x (-3 : ℤ) 1 = false := by simpa using h0
    exact cycle_power_thirty_one_double_false_bit_one_refuted_s5t_m3f x htight hexact hcover hcount hu0 hu1 hu2 h0
