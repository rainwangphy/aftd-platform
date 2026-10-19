import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RankingSwap

/-!
# is_adjacent_swap_bid

Topic: fair_division   Node: f6e3b47bb274

Provenance: formalization of a published result. Source: arXiv:2610.23040 Definition 3.6

Bid r of agent i is obtained from its current bid b i by an adjacent swap: exchanging two consecutive goods of the ranking.
-/

/-- Agent `i`'s bid `r` is obtained from its current bid `b i` by an adjacent swap (two consecutive goods exchanged). -/
def is_adjacent_swap_bid {N G : Type*} {m : ℕ} (b : N → Fin m ≃ G) (i : N) (r : Fin m ≃ G) : Prop :=
  ∃ (k : Fin m) (hk : k.val + 1 < m), r = ranking_swap (b i) k ⟨k.val + 1, hk⟩
