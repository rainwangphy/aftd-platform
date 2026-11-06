import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ExpectedChoreCost
import AFTD.Kb.GameTheoryEconomics.ChoreMaximinShare
import AFTD.Kb.GameTheoryEconomics.RandomizedOnlineChoreAlgorithm

/-!
# has_randomized_online_mms_barrier_breaker

Topic: fair_division   Node: 97bcfeb133d1

Provenance: formalization of a published result. Source: arXiv:2611.00432 Sec 4

There exists a strictly positive real ε > 0 and a randomized prediction-free online chore algorithm alg : RandomizedOnlineChoreAlgorithm n with upgrade recourse such that for every horizon m : ℕ and every nonnegative arrival cost profile c : Fin n → ℕ → ℝ, every agent i : Fin n has expected cost at most (2 - 1/n - ε) * chore_maximin_share n (fun d => c i d.val).
-/

/-- Property that a randomized online chore algorithm beats the 2 - 1/n MMS factor under upgrade recourse. -/
def has_randomized_online_mms_barrier_breaker (n : ℕ) : Prop :=
  ∃ (ε : ℝ) (_ : 0 < ε) (alg : RandomizedOnlineChoreAlgorithm n),
    ∀ (m : ℕ) (c : Fin n → ℕ → ℝ) (_ : ∀ i t, 0 ≤ c i t) (i : Fin n),
      expected_chore_cost alg c m i ≤
        (2 - 1 / (n : ℝ) - ε) * chore_maximin_share n (fun (d : Fin m) => c i d.val)
