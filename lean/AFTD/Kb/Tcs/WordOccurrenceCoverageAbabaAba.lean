import AFTD.Prelude
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# word_occurrence_coverage_ababa_aba

Topic: combinatorics   Node: bba84c90daa0

Provenance: helper lemma. Sanity lemma for word_occurrence_coverage: the example after Definition 3.1 of arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words).

The paper's example: in w = ababa the factor aba occurs at positions 1 and 3, so Cov_w(aba) = [1,3] ∪ [3,5] = [1,5] (letters a, b encoded as 0, 1).
-/

theorem word_occurrence_coverage_ababa_aba :
    word_occurrence_coverage [0, 1, 0, 1, 0] [0, 1, 0] = Finset.Icc 1 5 := by
  decide
