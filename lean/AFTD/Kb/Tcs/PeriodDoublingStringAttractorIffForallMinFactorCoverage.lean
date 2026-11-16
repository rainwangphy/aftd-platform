import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinset
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinsetMem
import AFTD.Kb.Tcs.IsStringAttractorIffForallMinFactorCoverage
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.PeriodDoublingWord

/-!
# period_doubling_string_attractor_iff_forall_min_factor_coverage

Topic: combinatorics   Node: 987e71da6a5d

Provenance: original. Related work: arXiv:2610.10950; arXiv:2602.16152

For every natural number n and every set of positions Γ ⊆ [1, (period_doubling_word n).length], Γ is a string attractor of the n-th period-doubling word period_doubling_word n if and only if Γ has nonempty intersection with every C in period_doubling_min_factor_coverages_finset n.
-/

/-- A set Γ ⊆ [1, |w_n|] is a string attractor of w_n iff Γ meets every inclusion-minimal factor coverage of w_n. -/
theorem period_doubling_string_attractor_iff_forall_min_factor_coverage
    (n : ℕ) (Γ : Finset ℕ) (hΓ : Γ ⊆ Finset.Icc 1 (period_doubling_word n).length) :
    is_string_attractor (period_doubling_word n) Γ ↔
      ∀ C ∈ period_doubling_min_factor_coverages_finset n, (Γ ∩ C).Nonempty := by
  rw [is_string_attractor_iff_forall_min_factor_coverage _ _ hΓ]
  simp_rw [period_doubling_min_factor_coverages_finset_mem]
