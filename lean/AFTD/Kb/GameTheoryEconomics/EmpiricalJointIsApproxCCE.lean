import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EmpiricalJoint
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColMarginal
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowDeviationLe
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointRowMarginal
import AFTD.Kb.GameTheoryEconomics.IsApproxCoarseCorrelatedEquilibrium
import AFTD.Kb.GameTheoryEconomics.EmpiricalJointColDeviationLe
import AFTD.Kb.GameTheoryEconomics.Game
import AFTD.Kb.GameTheoryEconomics.JointDistributionColDeviationUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionColExpectedUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowDeviationUtility
import AFTD.Kb.GameTheoryEconomics.JointDistributionRowExpectedUtility

/-!
# empiricalJoint_isApproxCCE

Topic: equilibria   Node: 11fef8893dd1

Provenance: formalization of a published result. Source: No-regret play yields an approximate coarse correlated equilibrium, as formalized in TCSlib (`empiricalJoint_isApproxCCE`). Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/CCE.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

No-regret play yields an approximate coarse correlated equilibrium. Let $G$ be a finite two-player game with row utility $u_r$ and column utility $u_c$ over
$M$ row actions and $N$ column actions, and consider $T > 0$ rounds of play in which the
row player uses the mixed strategy $p_t$ and the column player uses the mixed strategy
$q_t$ at round $t$. Fix $\varepsilon \in \bbr$, and suppose that for every pure row
deviation $i'$,
\[
  \sum_{t=1}^{T}\sum_{j}(q_t)_j\, u_r(i',j)
  \;-\; \sum_{t=1}^{T}\sum_{i,j}(p_t)_i (q_t)_j\, u_r(i,j)
  \;\le\; \varepsilon T,
\]
and for every pure column deviation $j'$,
\[
  \sum_{t=1}^{T}\sum_{i}(p_t)_i\, u_c(i,j')
  \;-\; \sum_{t=1}^{T}\sum_{i,j}(p_t)_i (q_t)_j\, u_c(i,j)
  \;\le\; \varepsilon T.
\]
Then the empirical joint distribution of the play, which assigns to each profile $(i,j)$
the probability $\frac{1}{T}\sum_{t=1}^{T}(p_t)_i (q_t)_j$, is an $\varepsilon$-coarse
correlated equilibrium of $G$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Finset BigOperators in
/-- No-regret dynamics yield a coarse correlated equilibrium: if over `T > 0` rounds of mixed play `p t`, `q t` both players have cumulative external regret at most `ε · T` against every fixed pure deviation (i.e. average regret at most `ε`), then the empirical joint distribution of their play is an `ε`-coarse correlated equilibrium of `G`. [Rou13-L17, Prop. 3.1 (no-regret dynamics converge to CCE)]; [CBL06, §7.4]. Deviation: stated for two players, with the regret hypotheses given as cumulative bounds `ε · T` for each player (the source's Proposition 3.1 states the hypothesis as time-averaged regret at most `ε` for every player and deviation; here it is written as the equivalent cumulative bound `ε · T`). **Proof sketch.** The proof is the term `⟨row, col⟩`: the row half is `empiricalJoint_row_deviation_le` applied to the row regret hypothesis at each deviation `i'`, and the column half is `empiricalJoint_col_deviation_le` applied to the column regret hypothesis at each deviation `j'`. Each half rewrites both sides as time averages, puts them over the common denominator `T`, clears `T`, and reads off the regret bound. -/
theorem empiricalJoint_isApproxCCE {M N T : ℕ} (hT : 0 < T)
    (G : Game M N)
    (p : Fin T → MixedStrategy M) (q : Fin T → MixedStrategy N)
    (ε : ℝ)
    (hRow : ∀ i' : Fin M,
      (∑ t : Fin T, ∑ j : Fin N, (q t).weights j * G.rowUtility i' j) -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.rowUtility i j) ≤ ε * T)
    (hCol : ∀ j' : Fin N,
      (∑ t : Fin T, ∑ i : Fin M, (p t).weights i * G.colUtility i j') -
        (∑ t : Fin T, ∑ i : Fin M, ∑ j : Fin N,
          (p t).weights i * (q t).weights j * G.colUtility i j) ≤ ε * T) :
    IsApproxCoarseCorrelatedEquilibrium G (empiricalJoint hT p q) ε :=
  -- Step 1: row half.  Step 2: column half.
  ⟨fun i' => empiricalJoint_row_deviation_le hT G p q ε i' (hRow i'),
   fun j' => empiricalJoint_col_deviation_le hT G p q ε j' (hCol j')⟩
