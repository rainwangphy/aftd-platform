import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallTight
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallExact
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallCover
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallBoundaryPairing

/-!
# cycle_power_dyadic_count_free_boundary_endpoint_counterexample

Topic: combinatorics   Node: 0462da2649f7

Provenance: helper lemma. Structural obstruction for research thread RT-1 and OP-205, arXiv:2610.15635.

There exists a radius-eight Boolean integer class model with tight classes, exact dyadic ownership, full ordinary distance coverage, and equal boundary bits at offsets 1 and 6 at every root, but whose class at root zero selects offset 3 while omitting offset 1. This drops pointwise optimal counts and periodicity and does not refute OP-205.
-/

theorem cycle_power_dyadic_count_free_boundary_endpoint_counterexample :
    ∃ x : ℤ → ℕ → Bool,
      (∀ p, cycle_power_dyadic_class_weight 3 (x p) =
        (Finset.range 8).sum (fun a => (x p a).toNat)) ∧
      (∀ j < 3, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+8-2^j)).toNat) = 1) ∧
      (∀ d : ℕ, 1 ≤ d → d < 8 → ∀ v : ℤ,
        ∃ a : ℕ, a < 8-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) ∧
      (∀ p : ℤ, x p 1 = x p 6) ∧
      x 0 1 = false ∧ x 0 3 = true := by
  refine ⟨cycle_power_dyadic_domain_wall,
    cycle_power_dyadic_domain_wall_tight, cycle_power_dyadic_domain_wall_exact,
    cycle_power_dyadic_domain_wall_cover, cycle_power_dyadic_domain_wall_boundary_pairing, ?_, ?_⟩ <;> decide
