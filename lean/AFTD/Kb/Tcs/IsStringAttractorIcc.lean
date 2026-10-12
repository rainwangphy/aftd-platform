import AFTD.Prelude
import AFTD.Kb.Tcs.IsStringAttractor
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverageNonempty
import AFTD.Kb.Tcs.WordOccurrenceCoverage

/-!
# is_string_attractor_Icc

Topic: combinatorics   Node: 0d8fc54ac20c

Provenance: helper lemma. Sanity lemma for is_string_attractor (arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Definition 3.1).

The set of all positions [1, |w|] is a string attractor of w.
-/

theorem is_string_attractor_Icc {α : Type*} [DecidableEq α] (w : List α) :
    is_string_attractor w (Finset.Icc 1 w.length) := by
  refine ⟨subset_rfl, fun x hx hxw => ?_⟩
  rw [Finset.inter_eq_right.2 (word_occurrence_coverage_subset w x)]
  exact word_occurrence_coverage_nonempty hx hxw
