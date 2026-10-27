import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicPruneExact
import AFTD.Kb.Tcs.CyclePowerDyadicPruneCover
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassPrune
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionSelf
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionCompPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_outer_projection_model

Topic: combinatorics   Node: c861e323d03d

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

Every valid direct outer projection preserves tight dyadic weight, exact dyadic edges and full ordinary coverage. No scalar active-count or colour preservation is asserted.
-/

open Finset

theorem cycle_power_dyadic_outer_projection_model
    (M r : ℕ) (hr : r ≤ M) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (M+1) (x p) =
      (range (2^(M+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < M+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(M+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(M+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(M+1)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true) :
    (∀ p, cycle_power_dyadic_class_weight (r+1) (cycle_power_dyadic_outer_projection (M+1) r (x p)) =
      (range (2^(r+1))).sum (fun a => (cycle_power_dyadic_outer_projection (M+1) r (x p) a).toNat)) ∧
    (∀ j < r+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (cycle_power_dyadic_outer_projection (M+1) r (x (v-(a : ℤ))) a &&
        cycle_power_dyadic_outer_projection (M+1) r (x (v-(a : ℤ))) (a+2^(r+1)-2^j)).toNat) = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^(r+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(r+1)-d ∧
        cycle_power_dyadic_outer_projection (M+1) r (x (v-(c : ℤ))) c = true ∧
        cycle_power_dyadic_outer_projection (M+1) r (x (v-(c : ℤ))) (c+d) = true) := by
  induction M generalizing r x with
  | zero =>
    have he : r=0 := by omega
    subst r
    simpa only [cycle_power_dyadic_outer_projection_self] using And.intro htight (And.intro hexact hcover)
  | succ M ih =>
    by_cases he : r=M+1
    · subst r
      simpa only [cycle_power_dyadic_outer_projection_self] using And.intro htight (And.intro hexact hcover)
    · let y : ℤ → ℕ → Bool := fun p => cycle_power_dyadic_b_lift M (x p)
      have hty := fun p => cycle_power_dyadic_tight_class_prune M (x p) (htight p)
      have hey := cycle_power_dyadic_prune_exact M x hexact
      have hcy := cycle_power_dyadic_prune_cover M x htight hcover
      have hs := ih r (by omega) y hty hey hcy
      have hpr (p : ℤ) : cycle_power_dyadic_outer_projection (M+1) r (y p) =
          cycle_power_dyadic_outer_projection (M+2) r (x p) :=
        cycle_power_dyadic_outer_projection_comp_prune M r (by omega) (x p)
      simpa only [hpr] using hs
