import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerEightPeriodSixModelWithoutCounts
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_eight_period_six_model_without_counts_valid

Topic: combinatorics   Node: 71a2dae00bf2

Provenance: helper lemma. Experiment 6094 in the OP-205 / RT-1 campaign, related to arXiv:2610.15635 Section 3. This finite countermodel refutes only omission of the active-count hypothesis, not OP-205. No research advance is claimed.

The explicit period-six model has endpoints, tight weights, exact dyadic edge coverage and full ordinary edge coverage, yet has a boundary mismatch and unequal active counts 3 and 5. This only refutes dropping the active-count condition from the auxiliary model.
-/

open Finset

theorem cycle_power_eight_period_six_model_without_counts_valid :
    (∀ p : ZMod 6, cycle_power_eight_period_six_model_without_counts p 0 = true ∧
      cycle_power_eight_period_six_model_without_counts p 7 = true) ∧
    (∀ p : ZMod 6, cycle_power_dyadic_class_weight 3 (cycle_power_eight_period_six_model_without_counts p) =
      (range 8).sum (fun j => (cycle_power_eight_period_six_model_without_counts p j).toNat)) ∧
    (∀ (j : Fin 3) (v : ZMod 6),
      (range (2 ^ j.val)).sum (fun a =>
        (cycle_power_eight_period_six_model_without_counts (v - (a : ZMod 6)) a &&
          cycle_power_eight_period_six_model_without_counts (v - (a : ZMod 6)) (a + 8 - 2 ^ j.val)).toNat) = 1) ∧
    (∀ (d : Fin 8), 0 < d.val → ∀ v : ZMod 6,
      ∃ a : Fin 8, a.val < 8 - d.val ∧
        cycle_power_eight_period_six_model_without_counts (v - (a.val : ZMod 6)) a.val = true ∧
        cycle_power_eight_period_six_model_without_counts (v - (a.val : ZMod 6)) (a.val + d.val) = true) ∧
    cycle_power_eight_period_six_model_without_counts 0 1 = true ∧
    cycle_power_eight_period_six_model_without_counts 0 6 = false ∧
    (range 8).sum (fun a => (cycle_power_eight_period_six_model_without_counts (-(a : ZMod 6)) a).toNat) = 3 ∧
    (range 8).sum (fun a => (cycle_power_eight_period_six_model_without_counts (1 - (a : ZMod 6)) a).toNat) = 5 := by
  decide
