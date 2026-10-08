import AFTD.Prelude
import AFTD.Kb.Tcs.Potential
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeWeightEqHedgeWeight
import AFTD.Kb.GameTheoryEconomics.PrefixPotential
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame

/-!
# prefixPotential_eq_potential

Topic: equilibria   Node: 6f1841cca524

Provenance: helper lemma. TCSlib, `prefixPotential_eq_potential`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prefix potential equals the induced Hedge potential. Let $G$ be a finite two-player zero-sum game with payoff matrix $A$ having $M$ rows and
$N$ columns, fix a learning rate $\eta \in \bbr$, and let $a_0, \dots, a_{T-1}$ be a
sequence of $T$ column actions. For any round $t < T$, the prefix potential of $G$ at
learning rate $\eta$ formed from the first $t$ column actions $a_0, \dots, a_{t-1}$
equals the Hedge potential at time $t$ of the loss sequence $\ell_s(i) = 1 - A_{i, a_s}$
induced on the row player by $G$ and the full sequence of column actions; that is, \[
\sum_{i \in \mathrm{Fin}\,M} \exp\!\Bigl(-\eta \sum_{s=0}^{t-1}\bigl(1 - A_{i,
a_s}\bigr)\Bigr) \;=\; \sum_{i \in \mathrm{Fin}\,M} \exp\!\bigl(-\eta\, L_t(i)\bigr), \]
where $L_t(i) = \sum_{s < t} \ell_s(i)$ is the cumulative loss of row $i$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The prefix potential over the first `t` actions equals `potential` at time `t` of the induced loss sequence. -/
lemma prefixPotential_eq_potential {M N T : ℕ} (G : ZeroSumGame M N)
    (η : ℝ) (actions : Fin T → Fin N) (t : Fin T) :
    prefixPotential G η
        (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) =
      potential η (G.toLossSeq actions) t.val := by
  simp only [prefixPotential, potential]
  apply Finset.sum_congr rfl
  intro i _
  exact prefixHedgeWeight_eq_hedgeWeight G η actions t i
