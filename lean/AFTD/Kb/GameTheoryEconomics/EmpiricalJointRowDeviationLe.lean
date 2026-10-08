import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowDeviationUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowExpectedUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowDeviationUtility
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowExpectedUtility
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal
import AFTD.Kb.Tcs.Regret

/-!
# empiricalJoint_row_deviation_le

Topic: equilibria   Node: 523c8c9826a4

Provenance: helper lemma. TCSlib, `empiricalJoint_row_deviation_le`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Row regret bound gives row deviation bound. Let $G$ be a finite two-player game with row utility $u_r$ over $M$ row actions and $N$
column actions, and consider $T > 0$ rounds of play in which the row player uses the
mixed strategy $p_t$ and the column player the mixed strategy $q_t$ at round $t$. Fix
$\varepsilon \in \bbr$ and a pure row action $i'$, and suppose the row player's
cumulative external regret against always playing $i'$ is at most $\varepsilon T$:
\[
  \sum_{t=1}^{T}\sum_{j}(q_t)_j\, u_r(i',j)
  \;-\; \sum_{t=1}^{T}\sum_{i,j}(p_t)_i (q_t)_j\, u_r(i,j)
  \;\le\; \varepsilon T.
\]
Then in the empirical joint distribution $\sigma$ of the play, deviating to $i'$ gains
at most $\varepsilon$ over the expected utility:
$\mathrm{rowDevUtil}(\sigma, G, i') \le \mathrm{rowExpUtil}(\sigma, G) + \varepsilon$.
This is the row half of  empiricalJoint_isApproxCCE.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- Row half of `empiricalJoint_isApproxCCE`: if the row player's cumulative external regret against the fixed deviation `i'` (the cumulative utility of always playing `i'` minus the actual cumulative expected utility) is at most `ε · T`, then in the empirical joint distribution deviating to `i'` gains at most `ε` over the expected utility. [Rou13-L17, Prop. 3.1]; [CBL06, §7.4]. **Proof sketch.** Step 1: rewrite both empirical utilities as time averages (`empiricalJoint_rowDeviationUtility`, `empiricalJoint_rowExpectedUtility`). Step 2: put the right-hand side over the common denominator `T`. Step 3: clear `T > 0` from both sides; the resulting inequality is the regret hypothesis. -/
lemma empiricalJoint_row_deviation_le {M N T : ℕ} (hT : 0 < T)
    (G : Game M N)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (ε : ℝ) (i' : Fin M)
    (hRow : (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) ≤ ε * T) :
    (empiricalJoint hT p q).rowDeviationUtility G i' ≤
      (empiricalJoint hT p q).rowExpectedUtility G + ε := by
  have hT_pos : (0 : ℝ) < (T : ℝ) := Nat.cast_pos.mpr hT
  have hT_ne : (T : ℝ) ≠ 0 := ne_of_gt hT_pos
  -- Step 1: rewrite both empirical utilities as time averages.
  rw [empiricalJoint_rowDeviationUtility, empiricalJoint_rowExpectedUtility]
  -- Step 2: put the right-hand side over the common denominator `T`.
  have hRHS :
      (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) / (T : ℝ) +
        ε =
        ((∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) +
          ε * (T : ℝ)) / (T : ℝ) := by field_simp
  -- Step 3: clear `T` and conclude from the regret bound.
  rw [hRHS, div_le_div_iff₀ hT_pos hT_pos]
  nlinarith [hRow, hT_pos]
