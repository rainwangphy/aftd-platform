import AFTD.Prelude
import AFTD.Kb.Tcs.IidWordMeasure
import AFTD.Kb.Tcs.BpeMinGreedyUtility
import AFTD.Kb.Tcs.BpeOptimalFullUtility
import AFTD.Kb.Tcs.IidBpeSharpFactor

/-!
# iid_greedy_bpe_approx_prob

Topic: algorithms   Node: 19254ef9b684

Provenance: original. Related work: folklore

Given alphabet size q, weights p : Fin q → ℝ, merge budget k, length N, and tolerance ε : ℝ, iid_greedy_bpe_approx_prob q p k N ε is the real probability under iid_word_measure q N p of the event that a word w : Fin N → Fin q has bpe_min_greedy_utility (List.ofFn (fun i => (w i : ℕ))) k ≥ (iid_bpe_sharp_factor - ε) * bpe_optimal_full_utility (List.ofFn (fun i => (w i : ℕ))) k.
-/

/-- Probability that length-N i.i.d. string achieves greedy k-merge utility at least (c - ε) times optimal full-merge utility. -/
noncomputable def iid_greedy_bpe_approx_prob (q : ℕ) (p : Fin q → ℝ) (k N : ℕ) (ε : ℝ) : ℝ := ((iid_word_measure q N p) {w : Fin N → Fin q | (bpe_min_greedy_utility (List.ofFn fun i => (w i : ℕ)) k : ℝ) ≥ (iid_bpe_sharp_factor - ε) * (bpe_optimal_full_utility (List.ofFn fun i => (w i : ℕ)) k : ℝ)}).toReal
