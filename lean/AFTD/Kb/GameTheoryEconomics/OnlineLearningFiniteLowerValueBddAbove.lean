import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningPayoffVsPureLeOne
import AFTD.Kb.GameTheoryEconomics.OnlineLearningPayoffVsPureNonneg
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# OnlineLearning.finiteLowerValue_bddAbove

Topic: equilibria   Node: 2d27218e08b7

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteLowerValue_bddAbove`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row player's guaranteed payoffs are bounded above. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N \ge 1$ column
actions, whose payoff matrix $(A_{ij})$ satisfies $0 \le A_{ij} \le 1$ for all $i,j$.
For a mixed row strategy $p = (p_i)$ over the $M$ rows, let $L(p) = \inf_{j} \sum_i p_i
A_{ij}$ be the least expected payoff against a pure column, taken over all $N$ columns.
Then the set $\{\, L(p) : p \text{ is a mixed strategy over the rows} \,\}$ is bounded
above.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The set of row-guaranteed finite-game payoffs is bounded above by one. -/
lemma OnlineLearning.finiteLowerValue_bddAbove {M N : ℕ} [NeZero N] (G : ZeroSumGame M N) :
    BddAbove (Set.range fun p : MixedStrategy M => ⨅ j : Fin N, payoffVsPure G p j) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨p, rfl⟩
  have hbdd : BddBelow (Set.range (payoffVsPure G p)) :=
    ⟨0, by rintro _ ⟨j, rfl⟩; exact payoffVsPure_nonneg G p j⟩
  exact (ciInf_le hbdd (Classical.choice inferInstance)).trans (payoffVsPure_le_one G p _)
