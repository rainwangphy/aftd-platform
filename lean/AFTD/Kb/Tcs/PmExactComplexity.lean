import AFTD.Prelude
import AFTD.Kb.Tcs.PMPoset
import AFTD.Kb.Tcs.PMPosetWidth2
import AFTD.Kb.Tcs.PMTree
import AFTD.Kb.Tcs.PMTreeCost
import AFTD.Kb.Tcs.PMTreeCorrect2
import AFTD.Kb.Tcs.PmLowerBound
import AFTD.Kb.Tcs.PmAlg
import AFTD.Kb.Tcs.PmAlgCorrect
import AFTD.Kb.Tcs.PmAlgCostLe

/-!
# pm_exact_complexity

Topic: algorithms   Node: e4a8c0de99e5

Exact deterministic complexity at width 2. For every n ≥ 2, the worst-case number of comparison queries needed by a deterministic algorithm to find all minimal elements of an n-element poset of width at most 2 is exactly 2n − 3: the candidate-list algorithm achieves it, and no correct algorithm does better.
-/

/-- **Exact deterministic complexity at width 2.** For every `n ≥ 2`, the worst-case number of comparison queries needed by a deterministic algorithm to find all minimal elements of an `n`-element poset of width at most `2` is exactly `2n − 3`: the candidate-list algorithm achieves it, and no correct algorithm does better. -/
theorem pm_exact_complexity (n : ℕ) (hn : 2 ≤ n) :
    (∃ T : PMTree n, T.Correct2 ∧ ∀ P : PMPoset n, P.Width2 → (T.cost P : ℤ) ≤ 2 * (n : ℤ) - 3)
    ∧ (∀ T : PMTree n, T.Correct2 → ∃ P : PMPoset n, P.Width2 ∧ 2 * (n : ℤ) - 3 ≤ T.cost P) :=
  ⟨⟨pmAlg n 0 [], pm_alg_correct n, fun P _ => pm_alg_cost_le n hn P⟩,
    fun T hT => pm_lower_bound T hT⟩
