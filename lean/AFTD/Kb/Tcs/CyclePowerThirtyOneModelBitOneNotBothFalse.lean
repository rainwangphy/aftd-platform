import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5f
import AFTD.Kb.Tcs.CyclePowerThirtyOneDoubleFalseBitOneRefutedS5t

/-!
# cycle_power_thirty_one_model_bit_one_not_both_false

Topic: combinatorics   Node: 5d8417a436e2

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case; one half of cycle_power_thirty_one_model_alternating (two consecutive classes without bit 1).

In a tight, exactly dyadically covered, fully covered exponent-5 model with 6 active classes per vertex, no two consecutive classes both lack bit 1: x(p,1) = false implies x(p+1,1) = true.
-/

-- uses RT1C32.model_shift from the s5f module

theorem cycle_power_thirty_one_model_bit_one_not_both_false (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1) :
    ∀ p : ℤ, x p 1 = false → x (p+1) 1 = true := by
  intro p hp
  by_contra hq
  have hq' : x (p+1) 1 = false := by simpa using hq
  obtain ⟨t, e, c, n⟩ := RT1C32.model_shift x ⟨htight, hexact, hcover, hcount⟩ p
  have h0 : (fun q a => x (p+q) a) (0 : ℤ) 1 = false := by simpa using hp
  have h1 : (fun q a => x (p+q) a) (1 : ℤ) 1 = false := by simpa using hq'
  by_cases hu : (fun q a => x (p+q) a) (5 : ℤ) 1 = true
  · exact cycle_power_thirty_one_double_false_bit_one_refuted_s5t (fun q a => x (p+q) a) t e c n h0 h1 hu
  · exact cycle_power_thirty_one_double_false_bit_one_refuted_s5f (fun q a => x (p+q) a) t e c n h0 h1
      (by simpa using hu)
