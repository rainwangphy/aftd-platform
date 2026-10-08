import AFTD.Prelude
import AFTD.Kb.Tcs.HedgeDist
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.GameTheoryEconomics.HedgeResponseNat
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeMixedStrategy
import AFTD.Kb.GameTheoryEconomics.PrefixHedgeMixedStrategyWeightEqHedgeDist
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.BestColumn
import AFTD.Kb.GameTheoryEconomics.BestColumnSpec
import AFTD.Kb.GameTheoryEconomics.PayoffVsPure

/-!
# hedgeResponseNat_isBestResponse

Topic: equilibria   Node: 07b3583b9759

Provenance: helper lemma. TCSlib, `hedgeResponseNat_isBestResponse`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Online column response is a best response. Let $G$ be a finite zero-sum game with $M \ge 1$ row actions and $N \ge 1$ column
actions, let $\eta \in \mathbb{R}$ be a learning rate, and let $T$ be a horizon.
Write $j_s =  hedgeResponseNat(G, \eta, s)$ for the online column
response at round $s$, and let $\ell =  ZeroSumGame.toLossSeq(G, (j_s)_{s < T})$
be the loss sequence it induces for the row player.  Then for every round
$t < T$ and every fixed column $j$,
\[
  \sum_{i}  hedgeDist(\eta, \ell, t)_i \, A(i, j_t)
  \;\le\;
  \sum_{i}  hedgeDist(\eta, \ell, t)_i \, A(i, j),
\]
i.e.\ the played column $j_t$ gives the row player, mixing according to the
Hedge distribution at round $t$, no more payoff than any other column.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- At each round, the online column response is a best response: against the Hedge distribution `hedgeDist η ℓ t` (where `ℓ` is the loss sequence induced by the responses themselves), the played column `hedgeResponseNat G η t` gives the row player no more payoff than any fixed column `j`. [FS99, §5, Eq. (10)]; [CBL06, proof of Thm 7.1]. **Proof sketch.** Step 1: the payoff of the prefix Hedge strategy against any column is the `hedgeDist`-weighted payoff sum at round `t`, by `prefixHedgeMixedStrategy_weight_eq_hedgeDist`. Step 2: by definition the played column is `bestColumn` of the prefix Hedge strategy. Step 3: `bestColumn_spec`, rewritten through Steps 1 and 2, is the claim. -/
lemma hedgeResponseNat_isBestResponse {M N T : ℕ} [NeZero M] [NeZero N]
    (G : ZeroSumGame M N) (η : ℝ) (t : Fin T) (j : Fin N) :
    ∑ i : Fin M, hedgeDist η (G.toLossSeq fun s : Fin T => hedgeResponseNat G η s.val) t.val i *
        G.payoff i (hedgeResponseNat G η t.val) ≤
      ∑ i : Fin M, hedgeDist η (G.toLossSeq fun s : Fin T => hedgeResponseNat G η s.val) t.val i *
        G.payoff i j := by
  let actions : Fin T → Fin N := fun s => hedgeResponseNat G η s.val
  -- Step 1: the prefix Hedge strategy's payoff against any column `j'` is the
  -- `hedgeDist`-weighted payoff sum at round `t`.
  have hpayoff : ∀ j' : Fin N,
      payoffVsPure G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) j' =
        ∑ i : Fin M, hedgeDist η (G.toLossSeq actions) t.val i * G.payoff i j' := by
    intro j'
    unfold payoffVsPure
    apply Finset.sum_congr rfl
    intro k _
    rw [prefixHedgeMixedStrategy_weight_eq_hedgeDist G η actions t k]
  -- Step 2: the played column is `bestColumn` of the prefix Hedge strategy.
  have haction :
      actions t =
        bestColumn G
          (prefixHedgeMixedStrategy G η
            (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) := by
    dsimp [actions]
    rw [hedgeResponseNat.eq_1]
  -- Step 3: `bestColumn_spec`, read through Steps 1 and 2.
  have hbc := bestColumn_spec G
    (prefixHedgeMixedStrategy G η
      (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩)) j
  rw [hpayoff, hpayoff, ← haction] at hbc
  exact hbc
