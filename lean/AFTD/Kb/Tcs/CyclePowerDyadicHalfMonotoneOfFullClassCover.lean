import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandMiddleImpFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicPruneFullClassCoverOfMiddleFullness
import AFTD.Kb.Tcs.CyclePowerDyadicExactHalfCover
import AFTD.Kb.Tcs.CyclePowerDyadicClassNoIslandOfFullClassCover
import AFTD.Kb.Tcs.CyclePowerDyadicHalfMonotoneOfMiddleFullAndPrunedMono
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_half_monotone_of_full_class_cover

Topic: combinatorics   Node: 3918ba4f7188

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

A tight exact full ordinary-cover dyadic integer model with a full class covering every vertex is monotone toward the endpoints separately on its two halves.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_dyadic_half_monotone_of_full_class_cover
    (m : ℕ) (hm : 1 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p : ℤ, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun i => (x p i).toNat))
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+d) = true)
    (hfullcover : ∀ v : ℤ, ∃ a : ℕ, a < 2^m ∧ ∀ i < 2^m, x (v-(a : ℤ)) i = true) :
    ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^(m-1) → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 2^(m-1) ≤ a → a ≤ b → b < 2^m → x p a = true → x p b = true) := by
  induction m using Nat.strong_induction_on generalizing x with
  | h m ih =>
    by_cases hm₂ : 2 ≤ m
    swap
    · have he : m = 1 := by omega
      subst m
      intro p
      constructor
      · intro a b hab hb hx
        have heq : a = b := by norm_num at hb; omega
        simpa only [heq] using hx
      · intro a b ha hab hb hx
        have heq : a = b := by norm_num at ha hb; omega
        simpa only [heq] using hx
    obtain ⟨k, rfl⟩ : ∃ k, m = k+2 := ⟨m-2, by omega⟩
    have hshape := cycle_power_dyadic_class_no_island_of_full_class_cover (k+2)
      (by omega) x htight hexact hcover hfullcover
    have hmid : ∀ (p : ℤ) (a : ℕ), 2^k ≤ a → a < 3*2^k → x p a = true →
        ∀ i < 2^(k+1), cycle_power_dyadic_b_lift k (x p) i = true := by
      intro p a ha hb hx
      exact cycle_power_dyadic_no_island_middle_imp_full_prune k (x p) (htight p)
        (hshape p) a ha hb hx
    let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift k (x p)
    have hyt := fun p => cycle_power_dyadic_tight_class_prune k (x p) (htight p)
    have hye := cycle_power_dyadic_prune_exact k x hexact
    have hyc := cycle_power_dyadic_prune_cover k x htight hcover
    have hyf := cycle_power_dyadic_prune_full_class_cover_of_middle_fullness k x hmid
      (cycle_power_dyadic_exact_half_cover k x hexact)
    have hprev := ih (k+1) (by omega) (by omega) y hyt hye hyc hyf
    have hprev' : ∀ p : ℤ,
        (∀ a b : ℕ, a ≤ b → b < 2^k → cycle_power_dyadic_b_lift k (x p) b = true →
          cycle_power_dyadic_b_lift k (x p) a = true) ∧
        (∀ a b : ℕ, 2^k ≤ a → a ≤ b → b < 2^(k+1) →
          cycle_power_dyadic_b_lift k (x p) a = true → cycle_power_dyadic_b_lift k (x p) b = true) := by
      simpa only [y, Nat.add_sub_cancel] using hprev
    simpa only [show k+2-1=k+1 by omega] using
      cycle_power_dyadic_half_monotone_of_middle_full_and_pruned_mono k x htight hexact hmid hcover hprev'
