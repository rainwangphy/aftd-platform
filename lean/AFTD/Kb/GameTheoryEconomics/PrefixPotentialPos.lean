import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeightPos
import AFTD.Kb.GameTheoryEconomics.PrefixPotential
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.Tcs.Potential

/-!
# prefixPotential_pos

Topic: equilibria   Node: 9e0ea7a9990f

Provenance: helper lemma. TCSlib, `prefixPotential_pos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the prefix potential. Let $G$ be a finite two-player zero-sum game with at least one row action, fix a
learning rate $\eta \in \bbr$, and let $a_0, \dots, a_{t-1}$ be any prefix of column
actions. Then the prefix potential is strictly positive,
\[
  \Phi_t \;=\; \sum_{i} \exp\!\bigl(-\eta\, L_t(i)\bigr) \;>\; 0,
\]
where $L_t(i)$ is the prefix cumulative loss of row $i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The prefix potential is strictly positive when there is at least one row, being a nonempty sum of positive weights. -/
lemma prefixPotential_pos {M N : ℕ} [NeZero M] (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) :
    0 < prefixPotential G η actions := by
  apply Finset.sum_pos
  · intro i _
    exact prefixHedgeWeight_pos G η actions i
  · exact Finset.univ_nonempty
