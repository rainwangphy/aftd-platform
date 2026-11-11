import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftAsymptoticVariance

/-!
# balanced_draft_variance_nonneg

Topic: fair_division   Node: 29108fd22ece

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The proposed asymptotic variance is nonnegative for at least two agents.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem balanced_draft_variance_nonneg (n : ℕ) (hn : 2 ≤ n) :
    0 ≤ balanced_draft_asymptotic_variance n := by
  unfold balanced_draft_asymptotic_variance
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn1 : 0 ≤ (n : ℝ) - 1 := by linarith
  positivity
