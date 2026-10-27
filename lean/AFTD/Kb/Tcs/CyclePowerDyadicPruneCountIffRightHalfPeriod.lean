import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCountBalance
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_prune_count_iff_right_half_period

Topic: combinatorics   Node: 88fe88b70722

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

Under the dyadic pruning balance hypotheses, preservation of active count t is equivalent to half-radius periodicity of right-half memberships.
-/

open Finset

theorem cycle_power_dyadic_prune_count_iff_right_half_period
    (k t : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k + 2) (x p) =
      (range (2 ^ (k + 2))).sum (fun a => (x p a).toNat))
    (hcount : ∀ v, (range (2 ^ (k + 2))).sum
      (fun a => (x (v - (a : ℤ)) a).toNat) = t + 1)
    (hhalf : ∀ v, (range (2 ^ (k + 1))).sum
      (fun a => (x (v - (a : ℤ)) a &&
        x (v - (a : ℤ)) (a + 2 ^ (k + 1))).toNat) = 1) :
    (∀ v, (range (2 ^ (k + 1))).sum (fun a =>
      (cycle_power_dyadic_b_lift k (x (v - (a : ℤ))) a).toNat) = t) ↔
    (∀ v, (range (2 ^ (k + 1))).sum (fun a =>
      (x ((v + (2 ^ (k + 1) : ℕ)) - ((2 ^ (k + 1) + a : ℕ) : ℤ))
        (2 ^ (k + 1) + a)).toNat) =
      (range (2 ^ (k + 1))).sum (fun a =>
        (x (v - ((2 ^ (k + 1) + a : ℕ) : ℤ)) (2 ^ (k + 1) + a)).toNat)) := by
  have hb := cycle_power_dyadic_prune_count_balance k t x htight hcount hhalf
  constructor
  · intro hc v
    have hh := hb v
    rw [hc v] at hh
    omega
  · intro hr v
    have hh := hb v
    rw [hr v] at hh
    omega
