import AFTD.Prelude
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.WordFactorCoverages

/-!
# word_min_factor_coverages_subset

Topic: combinatorics   Node: 0b601fba6c60

Provenance: helper lemma. Sanity lemma for word_min_factor_coverages (arXiv:2610.10950 (Smallest String Attractors and Minimal Coverage Certificates of Thue–Morse Words), Sec. 3.2).

Every inclusion-minimal factor coverage is a factor coverage: H_min(w) ⊆ H(w).
-/

theorem word_min_factor_coverages_subset {α : Type*} [DecidableEq α] (w : List α) :
    word_min_factor_coverages w ⊆ word_factor_coverages w :=
  fun _ hC => hC.1
