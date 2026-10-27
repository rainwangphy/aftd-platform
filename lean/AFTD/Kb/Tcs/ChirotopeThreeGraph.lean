import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.DiffersAtOneSymm
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.DiffersAtOneIrrefl
import AFTD.Kb.Tcs.IsRankThreeUniformChirotope
import AFTD.Kb.Tcs.DiffersAtOne
import AFTD.Kb.Tcs.OrderedTriple

/-!
# chirotope_three_graph

Topic: combinatorics   Node: 812ea069eb9b

Provenance: formalization of a published result. Source: arXiv:2610.03808 Def. 6.2

The mutation walk graph of uniform rank-3 chirotopes on Ω is the simple graph whose vertices are uniform rank-3 chirotopes chi : OrderedTriple Ω → ℤˣ (subtypes of functions satisfying is_rank_three_uniform_chirotope), with adjacency defined by differing at exactly one ordered triple via differs_at_one.
-/

/-- The mutation walk graph of uniform rank-3 chirotopes on Ω. -/
def chirotope_three_graph (Ω : Type*) [LinearOrder Ω] : SimpleGraph { chi : OrderedTriple Ω → ℤˣ // is_rank_three_uniform_chirotope chi } := {
  Adj := fun c₁ c₂ => differs_at_one c₁.val c₂.val
  symm := ⟨fun _ _ h => differs_at_one_symm h⟩
  loopless := ⟨fun c => differs_at_one_irrefl c.val⟩
}
