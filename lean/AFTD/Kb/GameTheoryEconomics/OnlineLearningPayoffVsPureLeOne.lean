import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# OnlineLearning.payoffVsPure_le_one

Topic: equilibria   Node: ccd521d14917

Provenance: helper lemma. TCSlib, `OnlineLearning.payoffVsPure_le_one`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expected payoff against a pure column is at most one. Let $G$ be a finite two-player zero-sum game whose payoff matrix $A$ has every entry in
$[0,1]$, let $p$ be a mixed row strategy with weights $p_i$, and let $j$ be a fixed pure
column action. Then the row player's expected payoff against column $j$ satisfies \[
\sum_i p_i \cdot A_{ij} \;\le\; 1. \]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Expected payoff against a pure column is at most one because every payoff is at most one and the row mixed strategy has total mass one. -/
lemma OnlineLearning.payoffVsPure_le_one {M N : ℕ} (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p j ≤ 1 := by
  calc payoffVsPure G p j
      ≤ ∑ i : Fin M, p.weights i * 1 :=
          Finset.sum_le_sum fun i _ =>
            mul_le_mul_of_nonneg_left (G.payoff_le_one i j) (p.nonneg i)
    _ = 1 := by simp [p.sum_one]
