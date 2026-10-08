import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeMixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.BestColumn

/-!
# hedgeResponseNat

Topic: equilibria   Node: 2c52ab3c2d3e

Provenance: formalization of a published result. Source: TCSlib, `hedgeResponseNat`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The sequence of column best responses generated online against Hedge: at time
$t$, given the history $a_0, \dots, a_{t-1}$ of prior column choices, the
column player responds with $a_t = \mathrm{bestColumn}(G, p_t)$, where $p_t$
is the prefix Hedge mixed strategy.  This is defined by well-founded recursion
on $t$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The column responses generated online against Hedge: at time `t`, the history consists of the earlier responses `s < t`; Hedge forms its mixed row strategy from that prefix, and the column player plays a pure best response (`bestColumn`) to that mixed strategy. Defined by well-founded recursion on `t`. [FS99, §5, Eq. (10) (the column player plays a best response to the row's multiplicative-weights distribution)]; [CBL06, proof of Thm 7.1]. -/
noncomputable def hedgeResponseNat {M N : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (η : ℝ) : ℕ → Fin N
  | t =>
      bestColumn G
        (prefixHedgeMixedStrategy G η (t := t)
          (fun s : Fin t => hedgeResponseNat G η s.val))
termination_by t => t
decreasing_by
  exact s.isLt
