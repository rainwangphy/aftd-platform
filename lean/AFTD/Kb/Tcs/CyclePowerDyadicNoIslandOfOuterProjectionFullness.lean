import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerNoIslandOfHalfMonotone
import AFTD.Kb.Tcs.CyclePowerDyadicHierarchyHalfMonotoneOfMiddleFullPrune
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjection
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionSelf
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionPrune
import AFTD.Kb.Tcs.CyclePowerDyadicOuterProjectionModel
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe

/-!
# cycle_power_dyadic_no_island_of_outer_projection_fullness

Topic: combinatorics   Node: 7889b3296d0b

Provenance: helper lemma. Uniform structural reduction for OP-205 / RT-1 following arXiv:2610.15635 Section 3. The all-scale shell fullness conditions are explicit hypotheses when used; they have not been derived from optimal active counts. No graph covering value or research advance is claimed.

A tight exact full-coverage model has no-island class shape if every selected middle bit at EVERY direct outer projection level forces the next prune to be full. Those all-scale fullness hypotheses remain explicit.
-/

open Finset

theorem cycle_power_dyadic_no_island_of_outer_projection_fullness
    (M : ℕ) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (M+1) (x p) =
      (range (2^(M+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < M+1, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(M+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(M+1) → ∀ v : ℤ,
      ∃ c : ℕ, c < 2^(M+1)-d ∧ x (v-(c : ℤ)) c = true ∧
        x (v-(c : ℤ)) (c+d) = true)
    (hfull : ∀ r < M, ∀ (p : ℤ) (a : ℕ), 2^r ≤ a → a < 3*2^r →
      cycle_power_dyadic_outer_projection (M+1) (r+1) (x p) a = true →
      ∀ i < 2^(r+1), cycle_power_dyadic_outer_projection (M+1) r (x p) i = true) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(M+1) →
      x p a = false → x p b = true → x p c = true := by
  let B : ℕ → ℤ → ℕ → Bool := fun r p => cycle_power_dyadic_outer_projection (M+1) r (x p)
  have hmodel := fun r hr => cycle_power_dyadic_outer_projection_model M r hr x htight hexact hcover
  have hpr (r : ℕ) (hr : r < M) (p : ℤ) (a : ℕ) :
      B r p a = cycle_power_dyadic_b_lift r (B (r+1) p) a := by
    have hh := cycle_power_dyadic_outer_projection_prune (M+1) r (by omega) (x p)
    exact (congrFun hh a).symm
  have hh := cycle_power_dyadic_hierarchy_half_monotone_of_middle_full_prune M B
    (fun r hr => (hmodel r hr).1) (fun r hr => (hmodel r hr).2.1)
    (fun r hr => (hmodel r hr).2.2) hpr hfull M (by omega)
  have hx : ∀ p : ℤ,
      (∀ a b : ℕ, a ≤ b → b < 2^M → x p b = true → x p a = true) ∧
      (∀ a b : ℕ, 2^M ≤ a → a ≤ b → b < 2^(M+1) →
        x p a = true → x p b = true) := by
    simpa only [B,cycle_power_dyadic_outer_projection_self] using hh
  exact cycle_power_no_island_of_half_monotone (2^M) (2^(M+1)) x hx
