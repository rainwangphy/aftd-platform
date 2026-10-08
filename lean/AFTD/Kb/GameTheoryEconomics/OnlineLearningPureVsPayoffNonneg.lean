import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# OnlineLearning.pureVsPayoff_nonneg

Topic: equilibria   Node: 049c05f9c6d7

Provenance: helper lemma. TCSlib, `OnlineLearning.pureVsPayoff_nonneg`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of a pure row's expected payoff. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, whose payoff matrix $A$ has entries satisfying $0 \le A_{ij} \le 1$. Fix a pure
row action $i$ and a mixed column strategy $q$, so its weights $q_j$ are non-negative
and sum to $1$. Then the expected payoff of row $i$ against $q$ is non-negative:
\[
  \sum_{j} A_{ij}\, q_j \;\ge\; 0.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Expected payoff of a pure row against a mixed column is nonnegative. -/
lemma OnlineLearning.pureVsPayoff_nonneg {M N : ℕ} (G : ZeroSumGame M N)
    (i : Fin M) (q : MixedStrategy N) :
    0 ≤ pureVsPayoff G i q := by
  exact Finset.sum_nonneg fun j _ =>
    mul_nonneg (G.payoff_nonneg i j) (q.nonneg j)
