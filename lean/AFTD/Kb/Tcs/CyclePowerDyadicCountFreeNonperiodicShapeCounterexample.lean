import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallTight
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallExact
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallCover
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallNotPeriodic

/-!
# cycle_power_dyadic_count_free_nonperiodic_shape_counterexample

Topic: combinatorics   Node: edbb5e205f68

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

There exists a genuinely nonperiodic tight radius-eight integer class system with exact dyadic edge ownership and coverage of every ordinary distance, but a selected island occurs at root zero and vertex-1 has five active classes. Thus dropping BOTH optimal original counts and periodicity permits islands. This does not refute the periodic count-free conjecture or OP-205.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_count_free_nonperiodic_shape_counterexample :
    ∃ x : ℤ → ℕ → Bool,
      (∀ p, cycle_power_dyadic_class_weight 3 (x p) =
        (range 8).sum (fun a => (x p a).toNat)) ∧
      (∀ j < 3, ∀ v : ℤ, (range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8-2^j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 8 → ∀ v : ℤ,
        ∃ a : ℕ, a < 8-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) ∧
      x 0 1 = false ∧ x 0 3 = true ∧ x 0 5 = false ∧
      (range 8).sum (fun a => (x (-1-(a : ℤ)) a).toNat) = 5 ∧
      (¬∃ n : ℕ, 0 < n ∧ ∀ (p : ℤ) (a : ℕ), x (p+(n : ℤ)) a = x p a) := by
  refine ⟨cycle_power_dyadic_domain_wall,
    cycle_power_dyadic_domain_wall_tight,
    cycle_power_dyadic_domain_wall_exact,
    cycle_power_dyadic_domain_wall_cover, ?_, ?_, ?_, ?_,
    cycle_power_dyadic_domain_wall_not_periodic⟩ <;> decide
