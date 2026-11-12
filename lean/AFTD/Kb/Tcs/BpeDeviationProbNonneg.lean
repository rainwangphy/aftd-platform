import AFTD.Prelude
import AFTD.Kb.Tcs.BpeDeviationProb
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli
import AFTD.Kb.Tcs.BpeGreedyRun
import AFTD.Kb.Tcs.BinaryEntropy
import AFTD.Kb.Tcs.WeightedMaxCutLinearCombination

/-!
# bpe_deviation_prob_nonneg

Topic: algorithms   Node: 3af88d3bb8ca

Provenance: helper lemma. step towards op_1533_iid_binary_greedy_bpe_universal_rate

For any source bias p ∈ (0, 1), step count k, input length N, target constant c, and tolerance ε, the deviation probability bpe_deviation_prob p hp k N c ε is ≥ 0.
-/

/-- The greedy BPE deviation probability is non-negative. -/
theorem bpe_deviation_prob_nonneg (p : ℝ) (hp : 0 < p ∧ p < 1) (k N : ℕ) (c ε : ℝ) : 0 ≤ bpe_deviation_prob p hp k N c ε := by first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination | (simp only [bpe_deviation_prob] at *; first | exact weighted_max_cut_linear_combination | (apply weighted_max_cut_linear_combination <;> assumption) | (apply weighted_max_cut_linear_combination <;> simp_all) | simpa using weighted_max_cut_linear_combination)
