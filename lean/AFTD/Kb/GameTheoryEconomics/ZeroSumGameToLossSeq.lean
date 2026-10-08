import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeq
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# ZeroSumGame.toLossSeq

Topic: equilibria   Node: 757e96518971

Provenance: formalization of a published result. Source: TCSlib, `ZeroSumGame.toLossSeq`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a game $G$ and a sequence of column responses $j_0, \dots, j_{T-1}$, the
induced \emph{loss sequence} for the row player is $\ell_t(i) = 1 - A_{i,j_t}
\in [0,1]$.  This translates a zero-sum game into the abstract loss-sequence
framework used by Hedge.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The loss sequence induced by a game and a sequence of column actions `j_t`: the loss of row `i` at round `t` is `1 − A(i, j_t)`, so that low loss means high payoff. [FS99, §§2–3 (there `M(i, j)` is already the row player's loss and the row player minimizes)]; [CBL06, proof of Thm 7.1]. Deviation: payoffs/row-maximizer convention, so the Hedge loss is `1 − A(i, j_t)`. -/
noncomputable def ZeroSumGame.toLossSeq {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : LossSeq M T :=
  fun t i => 1 - G.payoff i (colResponse t)
