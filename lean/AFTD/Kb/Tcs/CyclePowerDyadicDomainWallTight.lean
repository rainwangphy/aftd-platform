import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallLeft
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallRight

/-!
# cycle_power_dyadic_domain_wall_tight

Topic: combinatorics   Node: e9bf6fa4eb56

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

Every rooted profile in the explicit count-free nonperiodic radius-eight model is tight in the dyadic class-weight inequality.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_domain_wall_tight (p : ℤ) :
    cycle_power_dyadic_class_weight 3 (cycle_power_dyadic_domain_wall p) =
      (range 8).sum (fun a => (cycle_power_dyadic_domain_wall p a).toNat) := by
  by_cases hL : p ≤ -4
  · generalize hr : p % 4 = r
    have hr0 : 0 ≤ r := by omega
    have hr4 : r < 4 := by omega
    have hx : cycle_power_dyadic_domain_wall p =
        fun a => (if r % 2 = 0 then 129 else 243 : ℕ).testBit a := by
      funext a
      rw [cycle_power_dyadic_domain_wall_left p hL a]
      have he : p % 2 = r % 2 := by omega
      rw [he]
    rw [hx]
    interval_cases r <;> decide
  · by_cases hR : 4 ≤ p
    · generalize hr : p % 4 = r
      have hr0 : 0 ≤ r := by omega
      have hr4 : r < 4 := by omega
      have hx : cycle_power_dyadic_domain_wall p =
          fun a => (if r = 1 then 195 else if r = 3 then 255 else 129 : ℕ).testBit a := by
        funext a
        rw [cycle_power_dyadic_domain_wall_right p hR a, hr]
      rw [hx]
      interval_cases r <;> decide
    · have hlo : -3 ≤ p := by omega
      have hhi : p ≤ 3 := by omega
      interval_cases p <;> decide
