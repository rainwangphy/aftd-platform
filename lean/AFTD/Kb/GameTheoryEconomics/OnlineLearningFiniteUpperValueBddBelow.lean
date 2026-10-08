import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningPureVsPayoffLeOne
import AFTD.Kb.GameTheoryEconomics.OnlineLearningPureVsPayoffNonneg
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# OnlineLearning.finiteUpperValue_bddBelow

Topic: equilibria   Node: 76fe873c264a

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteUpperValue_bddBelow`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower boundedness of the row-supremum values. Let $G$ be a finite two-player zero-sum game with $M \ge 1$ row actions and $N$ column
actions, whose payoff matrix $A$ satisfies $A_{ij} \in [0,1]$ for all $i,j$. For a mixed
column strategy $q$ (a probability distribution on the $N$ columns), let
\[
  v(q) \;=\; \sup_{i}\, \sum_{j} A_{ij}\, q_j
\]
be the best expected payoff that a single pure row can achieve against $q$. Then the set
$\{\, v(q) : q \text{ a mixed column strategy}\,\}$ is bounded below.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The set of column-induced finite-game upper values is bounded below by zero. -/
lemma OnlineLearning.finiteUpperValue_bddBelow {M N : ℕ} [NeZero M] (G : ZeroSumGame M N) :
    BddBelow (Set.range fun q : MixedStrategy N => ⨆ i : Fin M, pureVsPayoff G i q) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨q, rfl⟩
  have hbdd : BddAbove (Set.range (fun i : Fin M => pureVsPayoff G i q)) :=
    ⟨1, by rintro _ ⟨i, rfl⟩; exact pureVsPayoff_le_one G i q⟩
  exact (pureVsPayoff_nonneg G (Classical.choice inferInstance) q).trans
    (le_ciSup hbdd (Classical.choice inferInstance))
