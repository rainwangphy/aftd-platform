import AFTD.Prelude
import AFTD.Kb.Tcs.WordMinFactorCoverages
import AFTD.Kb.Tcs.ThueMorseWord

/-!
# thue_morse_min_factor_coverages_finset

Topic: combinatorics   Node: 0e0bc235aea7

Provenance: helper lemma. step towards thue_morse_random_attractor_lattice_gumbel

The finite set of inclusion-minimal factor coverages H_min(t_n) of the n-th Thue-Morse word, realized as a Finset of subsets of the position set [1, 2^n].
-/

/-- H_min(t_n) as a Finset over the position set [1, 2^n], so the expected unhit count is a finite sum. -/
noncomputable def thue_morse_min_factor_coverages_finset (n : ℕ) : Finset (Finset ℕ) := by
  classical
  exact (Finset.Icc 1 (thue_morse_word n).length).powerset.filter
    (fun C => decide (C ∈ word_min_factor_coverages (thue_morse_word n)))
