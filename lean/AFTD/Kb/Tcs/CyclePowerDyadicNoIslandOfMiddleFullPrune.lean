import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicPruneFullClassCoverOfMiddleFullness
import AFTD.Kb.Tcs.CyclePowerNoIslandOfHalfMonotone
import AFTD.Kb.Tcs.CyclePowerDyadicExactHalfCover
import AFTD.Kb.Tcs.CyclePowerDyadicHalfMonotoneOfMiddleFullAndPrunedMono
import AFTD.Kb.Tcs.CyclePowerDyadicHalfMonotoneOfFullClassCover
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_of_middle_full_prune

Topic: combinatorics   Node: 1f1347a6cf23

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

In a tight exact full ordinary-cover dyadic integer model, current-scale middle-bit fullness alone implies that every class has no selected island between missing offsets. Smaller-scale fullness and active-count hypotheses are not assumed.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_no_island_of_middle_full_prune
    (k : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (k+2) (x p) =
      (range (2^(k+2))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < k+2, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(k+2)-2^j)).toNat) = 1)
    (hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
      ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(k+2) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(k+2)-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(k+2) →
      x p a = false → x p b = true → x p c = true := by
  let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift k (x p)
  have hyt := fun p => cycle_power_dyadic_tight_class_prune k (x p) (htight p)
  have hye := cycle_power_dyadic_prune_exact k x hexact
  have hyc := cycle_power_dyadic_prune_cover k x htight hcover
  have hyf := cycle_power_dyadic_prune_full_class_cover_of_middle_fullness k x hmid
    (cycle_power_dyadic_exact_half_cover k x hexact)
  have hprev := cycle_power_dyadic_half_monotone_of_full_class_cover (k+1)
    (by omega) y hyt hye hyc hyf
  have hprev' : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^k → cycle_power_dyadic_b_lift k (x p) b = true →
        cycle_power_dyadic_b_lift k (x p) a = true) ∧
      (∀ a b : ℕ, 2^k ≤ a → a ≤ b → b < 2^(k+1) →
        cycle_power_dyadic_b_lift k (x p) a = true → cycle_power_dyadic_b_lift k (x p) b = true) := by
    simpa only [y, Nat.add_sub_cancel] using hprev
  exact cycle_power_no_island_of_half_monotone (2^(k+1)) (2^(k+2)) x
    (cycle_power_dyadic_half_monotone_of_middle_full_and_pruned_mono
      k x htight hexact hmid hcover hprev')
