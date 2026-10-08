import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.JointDistributionColMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal

/-!
# empiricalJoint_colMarginal

Topic: equilibria   Node: 2f3f30962aa3

Provenance: helper lemma. TCSlib, `empiricalJoint_colMarginal`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column marginal of the empirical joint distribution. Consider $T > 0$ rounds of play between a row player with $M$ actions and a column
player with $N$ actions, where in round $t$ the row player uses the mixed strategy $p_t$
over the row actions and the column player uses the mixed strategy $q_t$ over the column
actions. Form the empirical joint distribution $\sigma$ assigning to each profile
$(i,j)$ the time-averaged probability $\frac{1}{T}\sum_{t=1}^{T} (p_t)_i (q_t)_j$. Then
for each column action $j$, the column marginal $\sigma^{\mathrm{col}}_j = \sum_i
\sigma_{ij}$ equals the time-average of the column player's weights on $j$,
\[
\sigma^{\mathrm{col}}_j = \frac{1}{T}\sum_{t=1}^{T} (q_t)_j.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The column marginal of the empirical joint distribution is the time-average of the column mixed strategies. -/
@[simp] lemma empiricalJoint_colMarginal {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (j : Fin N) :
    (empiricalJoint hT p q).colMarginal j =
      (∑ t : Fin T, (q t).weights j) / T := by
  show ∑ i : Fin M,
      (∑ t : Fin T, (p t).weights i * (q t).weights j) / (T : ℝ) =
    (∑ t : Fin T, (q t).weights j) / (T : ℝ)
  rw [← Finset.sum_div, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl; intro t _
  rw [← Finset.sum_mul, (p t).sum_one, one_mul]
