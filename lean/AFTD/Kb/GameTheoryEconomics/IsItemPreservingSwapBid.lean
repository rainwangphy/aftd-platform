import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingSwap
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome

/-!
# is_item_preserving_swap_bid

Topic: fair_division   Node: 44c423991b97

Provenance: formalization of a published result. Source: arXiv:2610.23040 Definition 3.7

Bid r of agent i is obtained from b i by an item-preserving swap: a swap of the goods in positions k < l that demotes the good g = b i k, where g is allocated to i both before and after the swap.
-/

/-- Agent `i`'s bid `r` is obtained from `b i` by an item-preserving swap: positions `k < l` exchanged, demoting the good `b i k`, which `i` receives both before and after the swap. -/
def is_item_preserving_swap_bid {N G : Type*} [DecidableEq N] [DecidableEq G] {m : ℕ}
    (seq : List N) (b : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G) : Prop :=
  ∃ k l : Fin m, k < l ∧ r = ranking_swap (b i) k l ∧
    b i k ∈ picking_sequence_outcome seq b i ∧
    b i k ∈ picking_sequence_outcome seq (Function.update b i r) i
