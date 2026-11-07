import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightParitySplit
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerDyadicBoundaryPairOfAlternating
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.CyclePowerSumRangeDouble
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_alternating_half_tight

Topic: combinatorics   Node: e2adb76a6992

Provenance: helper lemma. Helper for RT-1 (OP-205, arXiv:2610.15635): rungs of cycle_power_dyadic_alternating_half_model (the even and odd halves of the bit-1 classes of an alternating endpoint-only dyadic model form a model one exponent lower)

In a tight, exactly dyadically covered model at exponent m+1 (m >= 1) with alternating bit 1, for every class with bit 1 both its even half and its odd half are tight at exponent m (class weight equal to cardinality).
-/

theorem cycle_power_dyadic_alternating_half_tight (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (m+1) (x p) =
      (Finset.range (2^(m+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < (m+1), ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (p : ℤ) (hp : x p 1 = true) (e : ℕ) (he : e < 2) :
    cycle_power_dyadic_class_weight m (fun b => x p (2*b+e)) =
      (Finset.range (2^m)).sum (fun b => (x p (2*b+e)).toNat) := by
  have hend := cycle_power_dyadic_exact_endpoints (m+1) (by omega) x hexact p
  have hH := cycle_power_dyadic_boundary_pair_of_alternating (m+1) (by omega) x hexact halt p
  have hsplit := cycle_power_dyadic_class_weight_parity_split m hm (x p)
  rw [hend.1, hend.2, hH, hp, htight p] at hsplit
  have hpow : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; omega
  rw [hpow, cycle_power_sum_range_double, Finset.sum_add_distrib] at hsplit
  have hE := cycle_power_dyadic_class_weight_le m hm (fun i => x p (2 * i))
  have hO := cycle_power_dyadic_class_weight_le m hm (fun i => x p (2 * i + 1))
  simp only [Bool.and_self, Bool.toNat_true] at hsplit
  interval_cases e
  · simp only [Nat.add_zero]; omega
  · omega
