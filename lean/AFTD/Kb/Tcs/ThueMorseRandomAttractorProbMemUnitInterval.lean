import AFTD.Prelude
import AFTD.Kb.Tcs.ThueMorseRandomAttractorProb
import AFTD.Kb.Tcs.ThueMorseWordLength
import AFTD.Kb.Tcs.ThueMorseWord
import AFTD.Kb.Tcs.IsStringAttractor

/-!
# thue_morse_random_attractor_prob_mem_unit_interval

Topic: combinatorics   Node: 73bd6082e9cd

Provenance: helper lemma. step towards thue_morse_random_attractor_lattice_gumbel

For all n and k, 0 ≤ thue_morse_random_attractor_prob n k ≤ 1.
-/

/-- Each random-attractor probability lies in the unit interval. -/
theorem thue_morse_random_attractor_prob_mem_unit_interval (n k : ℕ) :
    thue_morse_random_attractor_prob n k ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  unfold thue_morse_random_attractor_prob
  constructor
  · positivity
  · have hpos : 0 < ((2 : ℝ) ^ n) ^ k := by positivity
    rw [div_le_one hpos]
    norm_cast
    refine le_trans (Finset.card_le_univ _) ?_
    simp
