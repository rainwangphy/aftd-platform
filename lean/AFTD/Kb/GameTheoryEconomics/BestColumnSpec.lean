import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.BestColumn
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# bestColumn_spec

Topic: equilibria   Node: 4e84cdc3370f

Provenance: helper lemma. TCSlib, `bestColumn_spec`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/ZeroSumGame.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Optimality of the column best response. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N \ge 1$ column
actions, given by a payoff matrix $A_{ij} \in [0,1]$, and let $p$ be a mixed strategy
for the row player, with weights $p_i$. Write $v(j) = \sum_i p_i A_{ij}$ for the
expected payoff of $p$ against the pure column $j$, and let $j^*$ be a column that
minimises $v$ over all $N$ columns. Then $v(j^*) \le v(j)$ for every column $j$; that
is, $j^*$ is indeed a minimiser of the expected payoff against $p$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The best-response column `bestColumn G p` does no worse for the column player than any other column: its payoff against `p` is at most the payoff of any column `j`. [FS99, §2 (best response)]. -/
lemma bestColumn_spec {M N : ℕ} [NeZero N] (G : ZeroSumGame M N)
    (p : MixedStrategy M) (j : Fin N) :
    payoffVsPure G p (bestColumn G p) ≤ payoffVsPure G p j := by
  exact (Classical.choose_spec (Finite.exists_min (payoffVsPure G p))) j
