import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteLowerValue
import AFTD.Kb.GameTheoryEconomics.OnlineLearningFiniteUpperValue
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.WeakDuality
import AFTD.Kb.GameTheoryEconomics.OnlineLearningMixedStrategyNonempty

/-!
# OnlineLearning.finiteLowerValue_le_upperValue

Topic: equilibria   Node: e6fdf3f78114

Provenance: helper lemma. TCSlib, `OnlineLearning.finiteLowerValue_le_upperValue`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ConvexMinimaxCore.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weak duality for finite zero-sum games. Let $G$ be a finite two-player zero-sum game with $M \geq 1$ row actions and $N \geq 1$
column actions, given by a payoff matrix $A_{ij} \in [0,1]$ that the row player seeks to
maximise and the column player to minimise. Then the lower value never exceeds the upper
value:
\[
  \sup_{p \in \Delta_M}\; \min_{j}\; \sum_{i} p_i A_{ij}
  \;\;\leq\;\;
  \inf_{q \in \Delta_N}\; \max_{i}\; \sum_{j} A_{ij} q_j,
\]
where $\Delta_M$ and $\Delta_N$ denote the sets of mixed strategies (probability
distributions) over the row and column actions, respectively.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Weak duality for finite games: the lower value is always at most the upper value. -/
lemma OnlineLearning.finiteLowerValue_le_upperValue {M N : ℕ} [NeZero M] [NeZero N] (G : ZeroSumGame M N) :
    finiteLowerValue G ≤ finiteUpperValue G := by
  unfold finiteLowerValue finiteUpperValue
  apply ciSup_le
  intro p
  apply le_ciInf
  intro q
  exact weak_duality G p q
