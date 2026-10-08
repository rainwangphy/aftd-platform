import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy

/-!
# empiricalJoint_rowMarginal

Topic: equilibria   Node: 9c84ea62912e

Provenance: helper lemma. TCSlib, `empiricalJoint_rowMarginal`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row marginal of the empirical joint distribution. Fix $T \ge 1$ rounds of play in which the row player uses mixed strategies
$p_1,\dots,p_T$ over $M$ actions and the column player uses mixed strategies
$q_1,\dots,q_T$ over $N$ actions, and let $\sigma$ be the empirical joint distribution,
which assigns to each profile $(i,j)$ the time-averaged probability
$\frac{1}{T}\sum_{t=1}^{T} (p_t)_i (q_t)_j$. Then for every row action $i$, the row
marginal $\sigma^{\mathrm{row}}_i = \sum_{j} \sigma_{ij}$ equals the time-average of the
row player's weight on $i$:
\[
\sigma^{\mathrm{row}}_i \;=\; \frac{1}{T}\sum_{t=1}^{T} (p_t)_i .
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The row marginal of the empirical joint distribution is the time-average of the row mixed strategies. -/
@[simp] lemma empiricalJoint_rowMarginal {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (i : Fin M) :
    (empiricalJoint hT p q).rowMarginal i =
      (∑ t : Fin T, (p t).weights i) / T := by
  show ∑ j : Fin N,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
    (∑ t : Fin T, (p t).weights i) / (T : ℝ)
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.mul_sum, (q t).sum_one, mul_one]
