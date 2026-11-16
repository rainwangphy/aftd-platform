import AFTD.Prelude
import AFTD.Kb.Tcs.PeriodDoublingMinFactorCoveragesFinset
import AFTD.Kb.Tcs.PeriodDoublingWord
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.WordMinFactorCoveragesSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordFactorCoverages

/-!
# period_doubling_min_factor_coverages_finset_mem

Topic: combinatorics   Node: 3a710b2a311a

Provenance: helper lemma. arXiv:2610.10950; arXiv:2602.16152

For every natural number n and every set of positions C, C belongs to period_doubling_min_factor_coverages_finset n if and only if C is an inclusion-minimal factor coverage of the n-th period-doubling word w_n.
-/

/-- A set C belongs to period_doubling_min_factor_coverages_finset n iff C is an inclusion-minimal factor coverage of w_n. -/
theorem period_doubling_min_factor_coverages_finset_mem (n : ℕ) (C : Finset ℕ) :
    C ∈ period_doubling_min_factor_coverages_finset n ↔ C ∈ word_min_factor_coverages (period_doubling_word n) := by
  dsimp [period_doubling_min_factor_coverages_finset]
  rw [Finset.mem_filter, Finset.mem_powerset]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hC := word_min_factor_coverages_subset (period_doubling_word n) h
    rcases hC with ⟨x, _, _, rfl⟩
    exact word_occurrence_coverage_subset (period_doubling_word n) x
