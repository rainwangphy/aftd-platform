import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallLeft
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallRight

/-!
# cycle_power_dyadic_domain_wall_boundary_pairing

Topic: combinatorics   Node: 1f2d55737bc6

Provenance: helper lemma. Structural obstruction for research thread RT-1 and OP-205, arXiv:2610.15635.

The existing radius-eight domain-wall Boolean class model has equal bits at offsets 1 and 6 at every integer root.
-/

theorem cycle_power_dyadic_domain_wall_boundary_pairing (p : ℤ) :
    cycle_power_dyadic_domain_wall p 1 = cycle_power_dyadic_domain_wall p 6 := by
  by_cases hL : p ≤ -4
  · rw [cycle_power_dyadic_domain_wall_left p hL 1, cycle_power_dyadic_domain_wall_left p hL 6]
    split <;> decide
  · by_cases hR : 4 ≤ p
    · rw [cycle_power_dyadic_domain_wall_right p hR 1, cycle_power_dyadic_domain_wall_right p hR 6]
      split <;> (try split) <;> decide
    · have hlo : -3 ≤ p := by omega
      have hhi : p ≤ 3 := by omega
      interval_cases p <;> decide
