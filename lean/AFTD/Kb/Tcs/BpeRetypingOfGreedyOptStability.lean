import AFTD.Prelude
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeOptimalUtility
import AFTD.Kb.Tcs.BpeGreedyStepLengthLe
import AFTD.Kb.Tcs.BpeGreedyStepsLengthLe
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep

/-!
# bpe_retyping_of_greedy_opt_stability

Topic: algorithms   Node: 2e4f068240a3

Provenance: helper lemma. Telescoping reduction from greedy one-step optimum stability to OP-1287.

Assume every greedy step loses at most twice its saving from the k-step optimal partial-merge utility, and assume k-step optimum is at most k times the initial maximum pair count. Then after any number of greedy steps, the original k-step optimum is at most twice the total greedy saving plus k times the maximum pair count in the resulting string.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

theorem bpe_retyping_of_greedy_opt_stability
    (hstable : ∀ (s t : List ℕ) (k : ℕ), bpe_greedy_step s t →
      bpe_optimal_utility s k ≤ 2 * (s.length - t.length) + bpe_optimal_utility t k)
    (hcount : ∀ (s : List ℕ) (k : ℕ),
      bpe_optimal_utility s k ≤ k * bpe_max_pair_count s)
    (i k : ℕ) (s t : List ℕ) (hg : bpe_steps bpe_greedy_step i s t) :
    bpe_optimal_utility s k ≤ 2 * (s.length - t.length) + k * bpe_max_pair_count t := by
  induction i generalizing s with
  | zero =>
      simp only [bpe_steps] at hg
      subst t
      simpa using hcount s k
  | succ i ih =>
      rcases hg with ⟨u, hu, hut⟩
      have h1 := hstable s u k hu
      have h2 := ih u hut
      have hlen1 := bpe_greedy_step_length_le s u hu
      have hlen2 := bpe_greedy_steps_length_le i u t hut
      omega
