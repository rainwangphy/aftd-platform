import AFTD.Prelude
import AFTD.Kb.Tcs.HedgeWeight
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.PrefixGameLossEqCumLoss
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeight
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixHedgeWeight_eq_hedgeWeight

Topic: equilibria   Node: 54ae05463cf7

Provenance: helper lemma. TCSlib, `prefixHedgeWeight_eq_hedgeWeight`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prefix Hedge weight agrees with the induced-loss Hedge weight. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, with payoff matrix $A$, let $\eta \in \bbr$ be a learning rate, and let $a_0,
\dots, a_{T-1}$ be a sequence of column actions, so that $a : \mathrm{Fin}\,T \to
\mathrm{Fin}\,N$. Fix a round $t \in \mathrm{Fin}\,T$ and a row $i \in \mathrm{Fin}\,M$.
Then the prefix Hedge weight of row $i$ at learning rate $\eta$, computed from the
length-$t$ prefix $a_0, \dots, a_{t-1}$ of column actions, equals the Hedge weight of
expert $i$ at time $t$ and learning rate $\eta$ for the loss sequence $\ell_s(j) = 1 -
A_{j, a_s}$ induced by $G$ along $a$; that is, both equal
\[
  \exp\!\Bigl(-\eta \sum_{s < t} \bigl(1 - A_{i, a_s}\bigr)\Bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The prefix Hedge weight of row `i` over the first `t` actions equals `hedgeWeight` at time `t` of the induced loss sequence. -/
lemma prefixHedgeWeight_eq_hedgeWeight {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    prefixHedgeWeight G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) i =
      hedgeWeight η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeWeight, hedgeWeight]
  rw [prefixGameLoss_eq_cumLoss]
