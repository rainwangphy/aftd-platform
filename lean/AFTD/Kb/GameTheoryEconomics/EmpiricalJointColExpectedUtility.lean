import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionColExpectedUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointSumProbMul
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal

/-!
# empiricalJoint_colExpectedUtility

Topic: equilibria   Node: 9d9a99becbca

Provenance: helper lemma. TCSlib, `empiricalJoint_colExpectedUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Column utility of the empirical joint distribution. Consider a finite two-player game with $M$ row actions and $N$ column actions, whose
column payoff is $u_c(i,j)$ for the action profile $(i,j)$. Fix $T \ge 1$ rounds in
which the row player plays the mixed strategy $p_t$ and the column player plays the
mixed strategy $q_t$, and let $\sigma$ be the empirical joint distribution, which
assigns to each profile $(i,j)$ the time-averaged probability $\frac{1}{T}\sum_{t=1}^{T}
(p_t)_i\,(q_t)_j$. Then the column player's expected utility under $\sigma$ equals the
time-average of the per-round bilinear column payoffs:
\[
  \sum_{i=1}^{M}\sum_{j=1}^{N} \sigma_{ij}\, u_c(i,j)
  = \frac{1}{T}\sum_{t=1}^{T}\sum_{i=1}^{M}\sum_{j=1}^{N} (p_t)_i\,(q_t)_j\, u_c(i,j).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The column player's expected utility under the empirical joint distribution is the time average of the column player's per-round expected utilities. -/
lemma empiricalJoint_colExpectedUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N) :
    (empiricalJoint hT p q).colExpectedUtility G =
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) / T :=
  empiricalJoint_sum_prob_mul hT p q G.colUtility
