import AFTD.Prelude
import AFTD.Kb.Tcs.LossSeqValid
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# ZeroSumGame.toLossSeq_valid

Topic: equilibria   Node: d13bc0a1bac6

Provenance: helper lemma. TCSlib, `ZeroSumGame.toLossSeq_valid`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Validity of the loss sequence induced by a zero-sum game. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, given by a payoff matrix $A$ whose entries satisfy $0 \le A_{ij} \le 1$, and
let $j_0, \dots, j_{T-1}$ be any sequence of column responses. Then the induced loss
sequence for the row player, defined by $\ell_t(i) = 1 - A_{i,j_t}$ for each round $t <
T$ and row action $i$, is valid: every loss lies in $[0,1]$, i.e. $0 \le \ell_t(i) \le
1$ for all $t$ and $i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The loss sequence induced by a game and a column-action sequence is a valid Hedge loss sequence: every loss `1 − A(i, j_t)` lies in `[0, 1]`, because payoffs do. [FS99, §§2–3]; [CBL06, proof of Thm 7.1]. -/
lemma ZeroSumGame.toLossSeq_valid {M N T : ℕ} (G : ZeroSumGame M N)
    (colResponse : Fin T → Fin N) : (G.toLossSeq colResponse).Valid := by
  -- Payoffs in `[0,1]` make `1 - payoff` a valid Hedge loss.
  intro t i; simp only [ZeroSumGame.toLossSeq]
  exact ⟨by linarith [G.payoff_le_one i (colResponse t)],
         by linarith [G.payoff_nonneg i (colResponse t)]⟩
