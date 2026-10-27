import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftLow
import AFTD.Kb.Tcs.CyclePowerDyadicBLiftHigh
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassMiddleParent
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_tight_class_parent

Topic: combinatorics   Node: fa7ceb4af535

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635 Section 3. These class-model, pruning and colour-rigidity lemmas do not establish the unresolved graph covering value. No research advance is claimed.

Equality in the dyadic class weight bound forces all rooted-tree parent implications at every smaller dyadic scale, uniformly in the arc length.
-/

open Finset

theorem cycle_power_dyadic_tight_class_parent
    (m j : ℕ) (hj : 1 ≤ j) (hjm : j < m) (b : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m b =
      (range (2 ^ m)).sum (fun a => (b a).toNat)) :
    ∀ a < 2 ^ j,
      (a < 2 ^ (j - 1) → b (a + 2 ^ m - 2 ^ j) = true → b a = true) ∧
      (2 ^ (j - 1) ≤ a → b a = true → b (a + 2 ^ m - 2 ^ j) = true) := by
  induction m using Nat.strong_induction_on generalizing j b with
  | h m ih =>
    have hm : 2 ≤ m := by omega
    obtain ⟨k, hk⟩ : ∃ k, m = k + 2 := ⟨m - 2, by omega⟩
    subst m
    have hH : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; omega
    have hD : 2 ^ (k + 2) = 2 * 2 ^ (k + 1) := by rw [pow_succ]; omega
    by_cases hjtop : j = k + 1
    · subst j
      have hp := cycle_power_dyadic_tight_class_middle_parent k b htight
      intro a ha
      have hindex : a + 2 ^ (k + 2) - 2 ^ (k + 1) = a + 2 ^ (k + 1) := by omega
      have hpred : k + 1 - 1 = k := by omega
      rw [hindex, hpred]
      constructor
      · intro haq hx
        have hh := hp.2 (a + 2 ^ (k + 1)) (by omega) (by omega) hx
        simpa only [Nat.add_sub_cancel_right] using hh
      · intro haq hx
        exact hp.1 a haq ha hx
    · have hjk : j ≤ k := by omega
      have hs := cycle_power_dyadic_tight_class_prune k b htight
      have hi := ih (k + 1) (by omega) j hj (by omega)
        (cycle_power_dyadic_b_lift k b) hs
      intro a ha
      have hh := hi a ha
      simpa only [cycle_power_dyadic_b_lift_low k j a hjk ha,
        cycle_power_dyadic_b_lift_high k j a hjk ha] using hh
