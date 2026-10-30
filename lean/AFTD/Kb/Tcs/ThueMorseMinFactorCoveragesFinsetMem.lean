import AFTD.Prelude
import AFTD.Kb.Tcs.ThueMorseMinFactorCoveragesFinset
import AFTD.Kb.Tcs.WordMinFactorCoveragesSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.WordFactorCoverages
import AFTD.Kb.Tcs.ThueMorseWord
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordMinFactorCoverages

/-!
# thue_morse_min_factor_coverages_finset_mem

Topic: combinatorics   Node: f33ff2aa6559

Provenance: helper lemma. step towards thue_morse_random_attractor_lattice_gumbel

For every n and every C, C belongs to thue_morse_min_factor_coverages_finset n if and only if C is an inclusion-minimal factor coverage of t_n.
-/

/-- Membership in the Finset realization of H_min(t_n) is exactly membership in the set H_min(t_n). -/
theorem thue_morse_min_factor_coverages_finset_mem (n : ℕ) (C : Finset ℕ) :
    C ∈ thue_morse_min_factor_coverages_finset n ↔ C ∈ word_min_factor_coverages (thue_morse_word n) := by
  dsimp [thue_morse_min_factor_coverages_finset]
  rw [Finset.mem_filter, Finset.mem_powerset]
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact h.2
  · intro h
    refine ⟨?_, h⟩
    have hC := word_min_factor_coverages_subset (thue_morse_word n) h
    rcases hC with ⟨x, _, _, rfl⟩
    exact word_occurrence_coverage_subset (thue_morse_word n) x
