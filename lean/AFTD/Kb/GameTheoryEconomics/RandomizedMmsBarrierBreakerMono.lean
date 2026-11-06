import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExpectedChoreCost
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.RandomizedOnlineChoreAlgorithm

/-!
# randomized_mms_barrier_breaker_mono

Topic: fair_division   Node: c152c876f55c

Provenance: helper lemma. arXiv:2611.00432 Sec 4

Monotonicity of the randomized MMS barrier guarantee: for any number of agents n : ℕ, real numbers ε' ≤ ε, and randomized online chore algorithm alg : RandomizedOnlineChoreAlgorithm n, if alg guarantees an expected cost at most (2 - 1/n - ε) * chore_maximin_share n (fun d => c i d.val) for all horizons m and nonnegative costs c, then for any m and nonnegative c where the maximin share is nonnegative, alg also guarantees expected cost at most (2 - 1/n - ε') * chore_maximin_share n (fun d => c i d.val).
-/

/-- Monotonicity of the randomized MMS approximation factor. -/
theorem randomized_mms_barrier_breaker_mono (n : ℕ) {ε ε' : ℝ} (hle : ε' ≤ ε)
    (alg : RandomizedOnlineChoreAlgorithm n)
    (h : ∀ (m : ℕ) (c : Fin n → ℕ → ℝ) (_ : ∀ i t, 0 ≤ c i t) (i : Fin n),
      expected_chore_cost alg c m i ≤
        (2 - 1 / (n : ℝ) - ε) * chore_maximin_share n (fun (d : Fin m) => c i d.val)) :
    ∀ (m : ℕ) (c : Fin n → ℕ → ℝ) (hc : ∀ i t, 0 ≤ c i t) (i : Fin n),
      0 ≤ chore_maximin_share n (fun (d : Fin m) => c i d.val) →
      expected_chore_cost alg c m i ≤
        (2 - 1 / (n : ℝ) - ε') * chore_maximin_share n (fun (d : Fin m) => c i d.val) := by
  intro m c hc i hM
  exact (h m c hc i).trans (by nlinarith)
