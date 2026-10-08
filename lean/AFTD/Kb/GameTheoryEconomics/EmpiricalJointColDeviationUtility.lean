import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionColDeviationUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal

/-!
# empiricalJoint_colDeviationUtility

Topic: equilibria   Node: a8856f756603

Provenance: helper lemma. TCSlib, `empiricalJoint_colDeviationUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column deviation utility of the empirical joint distribution. Let $G$ be a finite two-player game with $M$ row actions and $N$ column actions and
column utility $u_c(i,j)$, and fix a number of rounds $T \ge 1$. Suppose that in each
round $t \in \{1,\dots,T\}$ the row player plays a mixed strategy $p_t$ over the $M$ row
actions and the column player plays a mixed strategy $q_t$ over the $N$ column actions,
and let $\sigma$ be the empirical joint distribution that assigns mass
$\frac{1}{T}\sum_{t=1}^{T} (p_t)_i\,(q_t)_j$ to each action profile $(i,j)$. Then, for
every column action $j'$, the column player's expected utility from deviating to the
pure action $j'$ against the row marginal $\sigma^{\mathrm{row}}_i = \sum_{j}
\sigma_{ij}$ is the time average of the round-by-round deviation utilities:
\[
  \sum_{i} \sigma^{\mathrm{row}}_i\, u_c(i,j')
  = \frac{1}{T}\sum_{t=1}^{T}\sum_{i} (p_t)_i\, u_c(i,j').
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The column player's deviation utility in the empirical joint distribution is the time average `(1/T) Σ_t Σ_i p_t(i) v(i, j')` of the utility of always playing the fixed column action `j'` against the row strategies actually played. -/
lemma empiricalJoint_colDeviationUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N)
    (j' : Fin N) :
    (empiricalJoint hT p q).colDeviationUtility G j' =
      (∑ t : Fin T, ∑ i : Fin M, (p t).weights i * G.colUtility i j') / T := by
  unfold JointDistribution.colDeviationUtility
  simp_rw [empiricalJoint_rowMarginal]
  have hStep : ∀ i : Fin M,
      (∑ t : Fin T, (p t).weights i) / (T : ℝ) * G.colUtility i j' =
        (∑ t : Fin T, (p t).weights i * G.colUtility i j') / (T : ℝ) := by
    intro i
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [← Finset.sum_div, Finset.sum_comm]
