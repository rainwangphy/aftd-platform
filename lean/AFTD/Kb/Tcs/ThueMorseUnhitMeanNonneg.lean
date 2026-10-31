import AFTD.Prelude
import AFTD.Kb.Tcs.ThueMorseUnhitMean
import AFTD.Kb.Tcs.ThueMorseMinFactorCoveragesFinsetMem
import AFTD.Kb.Tcs.WordMinFactorCoveragesSubset
import AFTD.Kb.Tcs.WordOccurrenceCoverageSubset
import AFTD.Kb.Tcs.ThueMorseWordLength
import AFTD.Kb.Tcs.WordOccurrenceCoverage
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.ThueMorseMinFactorCoveragesFinset
import AFTD.Kb.Tcs.WordFactorCoverages
import AFTD.Kb.Tcs.ThueMorseWord

/-!
# thue_morse_unhit_mean_nonneg

Topic: combinatorics   Node: 2451298cce31

Provenance: helper lemma. step towards thue_morse_random_attractor_lattice_gumbel

For all n and k, 0 ≤ thue_morse_unhit_mean n k.
-/

/-- The expected unhit count is nonnegative, because every minimal coverage has size at most 2^n. -/
theorem thue_morse_unhit_mean_nonneg (n k : ℕ) : 0 ≤ thue_morse_unhit_mean n k := by
  unfold thue_morse_unhit_mean
  apply Finset.sum_nonneg
  intro C hC
  apply pow_nonneg
  rw [sub_nonneg]
  have hmem : C ∈ word_min_factor_coverages (thue_morse_word n) :=
    (thue_morse_min_factor_coverages_finset_mem n C).mp hC
  have hsub : C ⊆ Finset.Icc 1 (thue_morse_word n).length := by
    have h := word_min_factor_coverages_subset (thue_morse_word n) hmem
    simp only [word_factor_coverages, Set.mem_ofPred_eq] at h
    obtain ⟨x, _, _, hxC⟩ := h
    rw [← hxC]
    exact word_occurrence_coverage_subset (thue_morse_word n) x
  have hcard : C.card ≤ 2^n := by
    have := Finset.card_le_card hsub
    rwa [Nat.card_Icc, thue_morse_word_length] at this
  have h2pos : (0:ℝ) < 2^n := by positivity
  rw [div_le_one h2pos]
  exact_mod_cast hcard
