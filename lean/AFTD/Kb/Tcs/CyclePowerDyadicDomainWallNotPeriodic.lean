import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWall
import AFTD.Kb.Tcs.CyclePowerDyadicDomainWallRight

/-!
# cycle_power_dyadic_domain_wall_not_periodic

Topic: combinatorics   Node: d99f22f5f2b4

Provenance: helper lemma. OP-205 / RT-1 structural-hypothesis audit following arXiv:2610.15635. A compact five-exception version of the previously computed nonperiodic domain wall6554 was independently audited in experiment7315. This formal countermodel addresses a stronger auxiliary statement without counts or periodicity; it is not a graph cover, a periodic model, an OP-205 refutation, or a research advance.

The explicit integer rooted-profile model has no positive natural period.
-/

open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_dyadic_domain_wall_not_periodic :
    ¬∃ n : ℕ, 0 < n ∧ ∀ (p : ℤ) (a : ℕ),
      cycle_power_dyadic_domain_wall (p+(n : ℤ)) a = cycle_power_dyadic_domain_wall p a := by
  rintro ⟨n, hn, hp⟩
  have hper : Function.Periodic (fun p : ℤ => cycle_power_dyadic_domain_wall p 3) (n : ℤ) :=
    fun p => hp p 3
  have hh := hper.int_mul 4 0
  have hnZ : (1 : ℤ) ≤ (n : ℤ) := by omega
  have hmod : (4*(n : ℤ)) % 4 = 0 := by omega
  have hval : cycle_power_dyadic_domain_wall (4*(n : ℤ)) 3 = false := by
    rw [cycle_power_dyadic_domain_wall_right (4*(n : ℤ)) (by omega) 3, hmod]
    decide
  change cycle_power_dyadic_domain_wall (0+4*(n : ℤ)) 3 = cycle_power_dyadic_domain_wall 0 3 at hh
  simp only [zero_add, hval] at hh
  have hzero : cycle_power_dyadic_domain_wall 0 3 = true := by decide
  rw [hzero] at hh
  contradiction
