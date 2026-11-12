import AFTD.Prelude
import AFTD.Kb.Tcs.BpeGreedyRun
import AFTD.Kb.Tcs.BinaryEntropy
import AFTD.Kb.GameTheoryEconomics.BooleanProductBernoulli

/-!
# bpe_deviation_prob

Topic: algorithms   Node: 089b7ed46fbe

Provenance: original. Related work: knowledgebase, OP-1533: iid binary greedy bpe universal log dictionary rate

Given parameters (p : ℝ), hypothesis (hp : 0 < p ∧ p < 1), (k N : ℕ), and (c ε : ℝ), bpe_deviation_prob p hp k N c ε is the real number defined as the value in ℝ obtained by taking .toReal of the measure under boolean_product_bernoulli (Fin N) ⟨p, ⟨le_of_lt hp.1, le_of_lt hp.2⟩⟩ of the set of words w : Fin N → Bool for which there exists a list t : List ℕ such that bpe_greedy_run k (List.ofFn (fun i => if w i then 1 else 0)) t and ε < |binaryEntropy p * (N : ℝ) / ((t.length : ℝ) * Real.logb 2 (k + 2)) - c|.
-/

/-- Probability that a random binary string of length N has a k-step greedy BPE run deviating from rate c by more than ε. -/
noncomputable def bpe_deviation_prob (p : ℝ) (hp : 0 < p ∧ p < 1) (k N : ℕ) (c ε : ℝ) : ℝ :=
  let p_unit : unitInterval := ⟨p, ⟨le_of_lt hp.1, le_of_lt hp.2⟩⟩
  ((boolean_product_bernoulli (Fin N) p_unit) {w : Fin N → Bool |
    ∃ t : List ℕ, bpe_greedy_run k (List.ofFn (fun i => if w i then 1 else 0)) t ∧
      ε < |binaryEntropy p * (N : ℝ) / ((t.length : ℝ) * Real.logb 2 (k + 2)) - c|}).toReal
