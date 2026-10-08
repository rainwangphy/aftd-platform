import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# OnlineLearning.payoffVsPure_nonneg

Topic: equilibria   Node: 6170f6304a8a

Provenance: helper lemma. TCSlib, `OnlineLearning.payoffVsPure_nonneg`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Nonnegativity of the mixed payoff against a pure column. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, let $p$ be a mixed row strategy over the $M$ rows, and let $j$ be a pure column
action. Then the expected payoff of $p$ against column $j$ is non-negative:
\[
  \sum_{i} p_i \cdot A_{ij} \;\ge\; 0.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Expected payoff against a pure column is nonnegative because payoffs and mixed-strategy weights are nonnegative. -/
lemma OnlineLearning.payoffVsPure_nonneg {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    0 ≤ payoffVsPure G p j := by
  exact Finset.sum_nonneg fun i _ =>
    mul_nonneg (p.nonneg i) (G.payoff_nonneg i j)
