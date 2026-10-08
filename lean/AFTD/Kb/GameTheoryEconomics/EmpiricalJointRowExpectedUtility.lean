import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowExpectedUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointSumProbMul
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal

/-!
# empiricalJoint_rowExpectedUtility

Topic: equilibria   Node: 9b76f13e7b17

Provenance: helper lemma. TCSlib, `empiricalJoint_rowExpectedUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row expected utility of the empirical joint distribution. Fix a finite two-player game with $M$ row actions and $N$ column actions, and write
$u_r(i,j)$ for the row player's payoff at the pure profile $(i,j)$. Suppose that over $T
> 0$ rounds the row player plays a mixed strategy $p_t$ and the column player a mixed
strategy $q_t$ in each round $t$, and let $\sigma$ be the empirical joint distribution
given by $\sigma_{ij} = \frac{1}{T}\sum_{t=1}^{T}(p_t)_i\,(q_t)_j$. Then the row
player's expected utility under $\sigma$ equals the time-average of the per-round
bilinear payoffs:
\[
  \sum_{i,j}\sigma_{ij}\,u_r(i,j)
    = \frac{1}{T}\sum_{t=1}^{T}\sum_{i,j}(p_t)_i\,(q_t)_j\,u_r(i,j).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The row player's expected utility under the empirical joint distribution is the time average of the row player's per-round expected utilities `Σ_i Σ_j p_t(i) q_t(j) u(i, j)`. -/
lemma empiricalJoint_rowExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).rowExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.rowUtility
