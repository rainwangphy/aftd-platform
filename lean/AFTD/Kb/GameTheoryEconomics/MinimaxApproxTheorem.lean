import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ApproxMinimax
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure
import AFTD.Kb.GameTheoryEconomics.PureVsPayoff

/-!
# minimax_approx_theorem

Topic: equilibria   Node: 1abc55e5eeb0

Provenance: formalization of a published result. Source: Approximate minimax theorem for finite zero-sum games, as formalized in TCSlib (`minimax_approx_theorem`). Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/FiniteMinimax.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Approximate minimax theorem for finite zero-sum games. Let $G$ be a finite two-player zero-sum game with payoff matrix $A$, having at least two
row actions and at least one column action, and suppose every entry satisfies $0 \le
A_{ij} \le 1$. Then for every $\varepsilon > 0$ there exist a mixed row strategy $p$ and
a mixed column strategy $q$ such that, for every pure row $i$ and every pure column $j$,
\[
  \sum_{k} p_k \, A_{kj} + \varepsilon \;\ge\; \sum_{\ell} A_{i\ell} \, q_\ell.
\]
That is, the row player's guaranteed payoff under $p$ against any column falls short of
the column player's exposure under $q$ against any row by at most $\varepsilon$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The ε-approximate minimax theorem, quantified over all `ε`: for any game `G` with at least two row actions and every `ε > 0`, there exist mixed strategies `p`, `q` with `payoffVsPure G p j + ε ≥ pureVsPayoff G i q` for all pure `i`, `j`. This is `approx_minimax` with `ε` universally quantified. [CBL06, Thm 7.1 (finite case)]; [FS99, §5]. -/
theorem minimax_approx_theorem {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (hM : 1 < M) :
    ∀ ε : ℝ, 0 < ε →
      ∃ (p : MixedStrategy M) (q : MixedStrategy N),
        ∀ (i : Fin M) (j : Fin N),
          payoffVsPure G p j + ε ≥ pureVsPayoff G i q := by
  intro ε hε
  exact approx_minimax G hM ε hε
