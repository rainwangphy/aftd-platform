import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodDoublingWord
import AFTD.Kb.Tcs.WordMinFactorCoverages

/-!
# period_doubling_min_factor_coverages_finset

Topic: combinatorics   Node: 2d13e4595896

Provenance: original. Related work: arXiv:2610.10950; arXiv:2602.16152

For any natural number n, period_doubling_min_factor_coverages_finset n is the finite set of inclusion-minimal factor coverages H_min(w_n) of the n-th period-doubling word w_n, realized as a Finset of subsets of [1, |w_n|].
-/

/-- The finite set of inclusion-minimal factor coverages H_min(w_n) of the n-th period-doubling word w_n. -/
noncomputable def period_doubling_min_factor_coverages_finset (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 (period_doubling_word n).length).powerset.filter
    (fun C => decide (C ∈ word_min_factor_coverages (period_doubling_word n)))
