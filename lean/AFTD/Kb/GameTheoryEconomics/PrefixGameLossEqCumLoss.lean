import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PrefixGameLoss
import AFTD.Kb.GameTheoryEconomics.ZeroSumGame
import AFTD.Kb.GameTheoryEconomics.ZeroSumGameToLossSeq
import AFTD.Kb.Tcs.CumLoss

/-!
# prefixGameLoss_eq_cumLoss

Topic: equilibria   Node: 8bfd1ff2305b

Provenance: helper lemma. TCSlib, `prefixGameLoss_eq_cumLoss`. Lean proof by Karim Abdel Sadek, Mark Bedaywi, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/Minimax/HedgeInteraction.lean (Copyright (c) 2026 Karim Abdel Sadek and Mark Bedaywi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Prefix game loss equals induced cumulative loss. Let $G$ be a finite two-player zero-sum game with $M$ row actions and $N$ column
actions, given by a payoff matrix $A$ with $0 \le A_{ij} \le 1$, and let $a_0, \dots,
a_{T-1}$ be a sequence of column actions with each $a_s \in \mathrm{Fin}\,N$. Fix a row
action $i \in \mathrm{Fin}\,M$ and a round $t \in \mathrm{Fin}\,T$. Then the prefix
cumulative loss of row $i$ along the first $t$ column actions coincides with the
cumulative loss of expert $i$ through the first $t$ rounds of the loss sequence induced
by $G$ and $(a_s)_s$; that is,
\[
\sum_{s=0}^{t-1} \bigl(1 - A_{i,\,a_s}\bigr) \;=\; \sum_{s < t} \bigl(1 -
A_{i,\,a_s}\bigr).
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open Real Finset BigOperators in
/-- The prefix game loss of row `i` over the first `t` actions of a sequence of `T` column actions equals `cumLoss` at time `t` of the loss sequence induced by that sequence. **Proof sketch.** After unfolding, both sides are sums of the loss `1 − A(i, actions s)`: the left over all `s : Fin t`, the right over the rounds `s : Fin T` with `s < t`. Apply `Finset.sum_bij` with the inclusion `s ↦ ⟨s, _⟩ : Fin t → Fin T`: it lands in the filtered index set since `s < t`, it is injective (equal underlying values), every filtered index `b < t` is the image of `⟨b, _⟩`, and the summands agree definitionally. -/
lemma prefixGameLoss_eq_cumLoss {M N T : ℕ} (G : ZeroSumGame M N)
    (actions : Fin T → Fin N) (t : Fin T) (i : Fin M) :
    prefixGameLoss G (t := t.val) (fun s : Fin t.val => actions ⟨s.val, lt_trans s.isLt t.isLt⟩) i =
      cumLoss (G.toLossSeq actions) t.val i := by
  -- This identifies the recursive prefix view of the interaction with the
  -- `LossSeq` view expected by the generic Hedge theorem.
  simp only [prefixGameLoss, cumLoss, ZeroSumGame.toLossSeq]
  refine Finset.sum_bij
    (fun s (_ : s ∈ (Finset.univ : Finset (Fin t.val))) =>
      (⟨s.val, lt_trans s.isLt t.isLt⟩ : Fin T))
    ?mem ?eq ?inj ?surj
  · intro s _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact s.isLt
  · intro s _ b _ h
    have hv : (⟨s.val, lt_trans s.isLt t.isLt⟩ : Fin T).val =
        (⟨b.val, lt_trans b.isLt t.isLt⟩ : Fin T).val := congrArg Fin.val h
    exact Fin.ext hv
  · intro b hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
    refine ⟨⟨b.val, hb⟩, Finset.mem_univ _, ?_⟩
    exact Fin.ext rfl
  · intro s _
    rfl
