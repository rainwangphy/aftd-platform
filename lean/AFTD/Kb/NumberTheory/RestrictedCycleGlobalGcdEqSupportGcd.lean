import AFTD.Prelude
import AFTD.Kb.NumberTheory.FinitePowersetGcdSum
import AFTD.Kb.NumberTheory.RestrictedCycleExactSupportCount
import AFTD.Kb.NumberTheory.RestrictedCycleCountAsSupportSum
import AFTD.Kb.NumberTheory.FinitePowersetGcdComplement
import AFTD.Kb.NumberTheory.RestrictedCycleGlobalGcd
import AFTD.Kb.NumberTheory.RestrictedCyclePermsCount
import AFTD.Kb.NumberTheory.RestrictedCycleExcludedFamily

/-!
# restricted_cycle_global_gcd_eq_support_gcd

Topic: elementary_number_theory   Node: 971fb13284d0

Provenance: formalization of a published result. Source: arXiv:2610.40342v1 Proposition 11.3(i), first equality, with proof in Appendix A.5. Exact support counts are defined directly as cardinalities of permutations with that support; thus no unproved recurrence or cycle-type counting formula is assumed. This is a published reduction, not a solution of Question 14.10.

For every r and n, the global gcd of counts avoiding cycle lengths 1 through r and any additional subset of lengths up to n equals the gcd of the exact cycle-support counts over all supports contained in the interval r+1 through n.
-/

theorem restricted_cycle_global_gcd_eq_support_gcd (r n : ℕ) :
    restricted_cycle_global_gcd r n =
      (Finset.Icc (r+1) n).powerset.gcd (fun P => restricted_cycle_exact_support_count n P) := by
  classical
  unfold restricted_cycle_global_gcd restricted_cycle_excluded_family
  rw [Finset.gcd_image]
  calc
    _ = (Finset.Icc (r+1) n).powerset.gcd
        (fun A => restricted_cycle_perms_count n
          (Finset.Icc 1 r ∪ (Finset.Icc (r+1) n \ A))) :=
      (finite_powerset_gcd_complement (Finset.Icc (r+1) n)
        (fun T => restricted_cycle_perms_count n (Finset.Icc 1 r ∪ T))).symm
    _ = (Finset.Icc (r+1) n).powerset.gcd
        (fun A => ∑ P ∈ A.powerset, restricted_cycle_exact_support_count n P) := by
      apply Finset.gcd_congr rfl
      intro A hA
      exact restricted_cycle_count_as_support_sum r n A (Finset.mem_powerset.mp hA)
    _ = _ := finite_powerset_gcd_sum _ _
