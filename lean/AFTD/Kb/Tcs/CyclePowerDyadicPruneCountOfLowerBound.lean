import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodicCountEqOfShiftBalanceOfLowerBound
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCountBalance
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_count_of_lower_bound

Topic: combinatorics   Node: 867b982b30a6

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

In a finite periodic tight dyadic class model with original count t+1, a pointwise lower bound t on the pruned active counts implies exact preservation of count t.
-/

open Finset

theorem cycle_power_dyadic_prune_count_of_lower_bound
    (k n t : ℕ) (hn : 0 < n) (x : ℤ → ℕ → Bool)
    (hperiod : ∀ p j, x (p + (n : ℤ)) j = x p j)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k + 2) (x p) =
      (range (2 ^ (k + 2))).sum (fun a => (x p a).toNat))
    (hcount : ∀ v, (range (2 ^ (k + 2))).sum
      (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1)
    (hhalf : ∀ v, (range (2 ^ (k + 1))).sum
      (fun a => (x (v - (a : ℤ)) a &&
        x (v - (a : ℤ)) (a + 2 ^ (k + 1))).toNat) = 1)
    (hlower : ∀ v, t ≤ (range (2 ^ (k + 1))).sum (fun a =>
      (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a).toNat)) :
    ∀ v, (range (2 ^ (k + 1))).sum (fun a =>
      (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a).toNat) = t := by
  let C : ℤ → ℕ := fun v => (range (2 ^ (k + 1))).sum (fun a =>
    (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a).toNat)
  let R : ℤ → ℕ := fun v => (range (2 ^ (k + 1))).sum (fun a =>
    (x (v - ((2 ^ (k + 1) + a : ℕ) : ℤ)) (2 ^ (k + 1) + a)).toNat)
  have hpR : Function.Periodic R (n : ℤ) := by
    intro v
    apply sum_congr rfl
    intro a ha
    have heq : (v + (n : ℤ)) - ((2 ^ (k + 1) + a : ℕ) : ℤ) =
        (v - ((2 ^ (k + 1) + a : ℕ) : ℤ)) + (n : ℤ) := by ring
    rw [heq, hperiod]
  exact periodic_count_eq_of_shift_balance_of_lower_bound n t hn
    ((2 ^ (k + 1) : ℕ) : ℤ) C R hpR
    (cycle_power_dyadic_prune_count_balance k t x htight hcount hhalf) hlower
