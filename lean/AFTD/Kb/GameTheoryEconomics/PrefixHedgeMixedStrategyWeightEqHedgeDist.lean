import AFTD.Prelude
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeMixedStrategy
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeightEqHedgeWeight
import AFTD.Kb.GameTheoryEconomics.PrefixPotentialEqPotential
import AFTD.Kb.GameTheoryEconomics.MixedStrategy
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixHedgeMixedStrategy_weight_eq_hedgeDist

Topic: equilibria   Node: 4a7174365550

Provenance: helper lemma. TCSlib, `prefixHedgeMixedStrategy_weight_eq_hedgeDist`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prefix Hedge strategy agrees with the abstract Hedge distribution. Let $G$ be a finite two-player zero-sum game with $M \ge 1$ row actions and $N$ column
actions, fix a learning rate $\eta \in \bbr$, and let $a_0, \dots, a_{T-1}$ be a
sequence of column actions. For any round $t < T$ and any row $i$, the weight assigned
to $i$ by the prefix Hedge mixed strategy built from the length-$t$ prefix $a_0, \dots,
a_{t-1}$ equals the Hedge distribution value $p_t(i)$ obtained by running abstract
Hedge, at the same learning rate $\eta$, on the loss sequence $\ell$ induced by $G$ and
$a$, namely $\ell_s(i) = 1 - A_{i, a_s}$. In symbols, both sides equal $w_t(i)/\Phi_t$,
where $w_t(i) = \exp(-\eta \sum_{s<t}(1 - A_{i,a_s}))$ and $\Phi_t = \sum_{k} w_t(k)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The weights of the prefix Hedge mixed strategy over the first `t` actions equal `hedgeDist` at time `t` of the induced loss sequence. -/
lemma prefixHedgeMixedStrategy_weight_eq_hedgeDist {M N T : ℕ} [NeZero M]
    (G : ZeroSumGame M N) (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    (prefixHedgeMixedStrategy G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)).weights i =
      hedgeDist η (G.toLossSeq actions) t.val i := by
  simp only [prefixHedgeMixedStrategy, hedgeDist]
  rw [prefixHedgeWeight_eq_hedgeWeight, prefixPotential_eq_potential]
