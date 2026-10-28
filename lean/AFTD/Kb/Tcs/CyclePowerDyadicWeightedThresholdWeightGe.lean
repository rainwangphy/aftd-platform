import AFTD.Prelude
import AFTD.Kb.Tcs.BoolWeightedMixtureThresholdDominates
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_weighted_threshold_weight_ge

Topic: combinatorics   Node: 11ed84546dcd

Provenance: helper lemma. Standard finite common-threshold coupling, formalized as a helper for OP-205 / RT-1, arXiv:2610.15635. Used to compress whole-class linear relaxations. This does not prove the remaining shape implication and is not claimed novel or research-level.

Common-threshold coupling of any finite natural-weighted mixture of dyadic profiles cannot decrease total dyadic class weight.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_weighted_threshold_weight_ge
    {ι : Type*} (m : ℕ) (S : Finset ι) (w : ι → ℕ) (B : ι → ℕ → Bool) :
    let N := S.sum w
    let c := fun j => S.sum (fun i => w i * (B i j).toNat)
    S.sum (fun i => w i * cycle_power_dyadic_class_weight m (B i)) ≤
      (range N).sum (fun r => cycle_power_dyadic_class_weight m
        (fun j => decide (r < c j))) := by
  dsimp only
  let N := S.sum w
  let c := fun j => S.sum (fun i => w i * (B i j).toNat)
  let T := fun r j => decide (r < c j)
  have hdom := (bool_weighted_mixture_threshold_dominates S w B).2.1
  have hends : (S.sum (fun i => w i * (2 * (B i 0 && B i (2^m-1)).toNat))) ≤
      (range N).sum (fun r => 2 * (T r 0 && T r (2^m-1)).toNat) := by
    have h := Nat.mul_le_mul_left 2 (hdom 0 (2^m-1))
    simpa only [mul_sum, T, c, N, mul_left_comm] using h
  have hrest :
      S.sum (fun i => w i * (range m).sum (fun j => if j=0 then 0 else
        (range (2^j)).sum (fun a => (B i a && B i (a+2^m-2^j)).toNat))) ≤
      (range N).sum (fun r => (range m).sum (fun j => if j=0 then 0 else
        (range (2^j)).sum (fun a => (T r a && T r (a+2^m-2^j)).toNat))) := by
    simp only [mul_sum]
    conv_lhs => rw [sum_comm]
    conv_rhs => rw [sum_comm]
    apply sum_le_sum
    intro j hj
    by_cases hj0 : j=0
    · simp [hj0]
    · simp only [hj0, ↓reduceIte, mul_sum]
      conv_lhs => rw [sum_comm]
      conv_rhs => rw [sum_comm]
      exact sum_le_sum (fun a ha => hdom a (a+2^m-2^j))
  simp only [cycle_power_dyadic_class_weight, mul_add, sum_add_distrib]
  exact add_le_add hends hrest
