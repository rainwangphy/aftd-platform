import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowDeviationUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal

/-!
# empiricalJoint_rowDeviationUtility

Topic: equilibria   Node: 8e98ef38c8fa

Provenance: helper lemma. TCSlib, `empiricalJoint_rowDeviationUtility`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Empirical row deviation utility as a time average. Let $G$ be a finite two-player game with $M$ row actions and $N$ column actions, and let
$u_r(i,j)$ denote the row player's utility. Fix an integer $T \ge 1$, and suppose that
in each round $t \in \{1,\dots,T\}$ the row player plays the mixed strategy $p_t$ over
the $M$ row actions and the column player plays the mixed strategy $q_t$ over the $N$
column actions, giving rise to the empirical joint distribution $\sigma$ with
$\sigma_{ij} = \tfrac{1}{T}\sum_{t=1}^{T} (p_t)_i\,(q_t)_j$. Then for every pure row
action $i'$, the row player's deviation utility under $\sigma$ equals the time average
of the expected utilities of playing $i'$ against each round's column strategy:
\[
  \sum_{j} \sigma^{\mathrm{col}}_j\, u_r(i',j)
  = \frac{1}{T}\sum_{t=1}^{T}\sum_{j} (q_t)_j\, u_r(i',j).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- The row player's deviation utility in the empirical joint distribution is the time average `(1/T) Σ_t Σ_j q_t(j) u(i', j)` of the utility of always playing the fixed row action `i'` against the column strategies actually played. -/
lemma empiricalJoint_rowDeviationUtility {M N T : ℕ} (hT : 0 < T)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N) (G : Game M N)
    (i' : Fin M) :
    (empiricalJoint hT p q).rowDeviationUtility G i' =
      (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) / T := by
  unfold JointDistribution.rowDeviationUtility
  simp_rw [empiricalJoint_colMarginal]
  have hStep : ∀ j : Fin N,
      (∑ t : Fin T, (q t).weights j) / (T : ℝ) * G.rowUtility i' j =
        (∑ t : Fin T, (q t).weights j * G.rowUtility i' j) / (T : ℝ) := by
    intro j
    rw [div_mul_eq_mul_div, ← Finset.sum_mul]
  simp_rw [hStep]
  rw [← Finset.sum_div, Finset.sum_comm]
