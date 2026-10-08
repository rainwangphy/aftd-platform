import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeight
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixHedgeWeight_pos

Topic: equilibria   Node: 8563f0e79eeb

Provenance: helper lemma. TCSlib, `prefixHedgeWeight_pos`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positivity of the prefix Hedge weight. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, let $\eta \in \bbr$ be a learning rate, and fix any prefix $a_0, \dots,
a_{t-1}$ of $t$ column actions together with a row $i$. Then the prefix Hedge weight
$w_t(i) = \exp\!\bigl(-\eta \cdot L_t(i)\bigr)$ is strictly positive, where $L_t(i) =
\sum_{s=0}^{t-1}\bigl(1 - A_{i,a_s}\bigr)$ is the prefix cumulative loss of row $i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- Every prefix Hedge weight is strictly positive, being an exponential. -/
lemma prefixHedgeWeight_pos {M N : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) {t : ℕ} (actions : Fin t → Fin N) (i : Fin M) :
    0 < prefixHedgeWeight G η actions i :=
  Real.exp_pos _
