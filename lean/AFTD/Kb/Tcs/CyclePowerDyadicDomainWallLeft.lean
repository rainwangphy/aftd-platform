import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall

/-!
# cycle_power_dyadic_domain_wall_left

Topic: combinatorics   Node: 04459500e9a0

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

For roots at most-4, the explicit domain-wall profile equals its two-periodic left tail.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_domain_wall_left
    (p : ℤ) (hp : p ≤ -4) (a : ℕ) :
    cycle_power_dyadic_domain_wall p a =
      (if p % 2 = 0 then 129 else 243 : ℕ).testBit a := by
  have hA : p ≠ -3 := by omega
  have hB : p ≠ -1 := by omega
  have hC : p ≠ 0 := by omega
  have hD : p ≠ 1 := by omega
  have hE : p ≠ 3 := by omega
  have hN : p < 0 := by omega
  simp only [cycle_power_dyadic_domain_wall, if_neg hA, if_neg hB,
    if_neg hC, if_neg hD, if_neg hE, if_pos hN]
