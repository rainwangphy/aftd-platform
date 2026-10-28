import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallCoverSum

/-!
# cycle_power_dyadic_domain_wall_cover

Topic: combinatorics   Node: 99f6747f7d65

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

Every edge of every positive distance below eight is covered by the explicit integer rooted-profile model.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_domain_wall_cover
    (d : ℕ) (hd : 1 ≤ d) (hd8 : d < 8) (v : ℤ) :
    ∃ a : ℕ, a < 8-d ∧ cycle_power_dyadic_domain_wall (v-(a : ℤ)) a = true ∧
      cycle_power_dyadic_domain_wall (v-(a : ℤ)) (a+d) = true := by
  classical
  have hpos := cycle_power_dyadic_domain_wall_cover_sum d hd hd8 v
  by_contra hno
  have hzero : (range (8-d)).sum (fun a =>
      (cycle_power_dyadic_domain_wall (v-(a : ℤ)) a &&
        cycle_power_dyadic_domain_wall (v-(a : ℤ)) (a+d)).toNat) = 0 := by
    apply sum_eq_zero
    intro a ha
    have hnot : ¬(cycle_power_dyadic_domain_wall (v-(a : ℤ)) a = true ∧
        cycle_power_dyadic_domain_wall (v-(a : ℤ)) (a+d) = true) := by
      rintro ⟨h0, h1⟩
      exact hno ⟨a, mem_range.mp ha, h0, h1⟩
    cases h0 : cycle_power_dyadic_domain_wall (v-(a : ℤ)) a <;>
      cases h1 : cycle_power_dyadic_domain_wall (v-(a : ℤ)) (a+d) <;> simp_all
  omega
