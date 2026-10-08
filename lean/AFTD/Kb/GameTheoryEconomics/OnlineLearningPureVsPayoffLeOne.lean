import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# OnlineLearning.pureVsPayoff_le_one

Topic: equilibria   Node: 6777a4d5ef1e

Provenance: helper lemma. TCSlib, `OnlineLearning.pureVsPayoff_le_one`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pure row payoff against a mixed column is at most one. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, whose payoff matrix $A$ satisfies $0 \le A_{ij} \le 1$ for all entries, and let
$q$ be a mixed column strategy, that is, a probability distribution $q_1, \dots, q_N$
over the columns. Then for every pure row action $i$, the expected payoff of row $i$
against $q$ satisfies
\[
  \sum_{j} A_{ij}\, q_j \;\le\; 1.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Expected payoff of a pure row against a mixed column is at most one. -/
lemma OnlineLearning.pureVsPayoff_le_one {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) :
    pureVsPayoff G i q ≤ 1 := by
  calc pureVsPayoff G i q
      ≤ ∑ j : Fin N, 1 * q.weights j :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_right (G.payoff_le_one i j) (q.nonneg j)
    _ = 1 := by simp [q.sum_one]
