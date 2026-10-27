import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.DiffersAtOneSymm
import AFTD.Kb.Tcs.IsRankThreeSignotope
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.DiffersAtOneIrrefl
import AFTD.Kb.Tcs.DiffersAtOne
import AFTD.Kb.Tcs.OrderedTriple

/-!
# bruhat_order_three_graph

Topic: combinatorics   Node: 92bf4b1efd2b

Provenance: formalization of a published result. Source: arXiv:2610.03808 Def. 6.7

The higher Bruhat order B(α, 2) is the simple graph whose vertices are rank-3 signotopes u : OrderedTriple α → ℤˣ (subtypes of functions satisfying is_rank_three_signotope), with adjacency defined by differing at exactly one ordered triple via differs_at_one.
-/

/-- The higher Bruhat order B(α, 2) viewed as an undirected flip graph of rank-3 signotopes. -/
def bruhat_order_three_graph (α : Type*) [LinearOrder α] : SimpleGraph { u : OrderedTriple α → ℤˣ // is_rank_three_signotope u } := {
  Adj := fun u v => differs_at_one u.val v.val
  symm := ⟨fun _ _ h => differs_at_one_symm h⟩
  loopless := ⟨fun u => differs_at_one_irrefl u.val⟩
}
