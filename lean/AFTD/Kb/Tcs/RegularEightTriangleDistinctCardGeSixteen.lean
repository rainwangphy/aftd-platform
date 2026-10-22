import AFTD.Prelude
import AFTD.Kb.Tcs.RegularEightTriangleDistinctCardGeFifteen
import AFTD.Kb.Tcs.SimpleGraphEightRegularNotCardFifteen
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct

/-!
# regular_eight_triangle_distinct_card_ge_sixteen

Topic: graphs   Node: 1408d4f9c0f5

Provenance: helper lemma. step towards regular_eight_triangle_distinct_witness

Every nonempty 8-regular triangle-distinct graph has at least 16 vertices, tightening the previous lower bound of 15.
-/

/-- Every nonempty 8-regular triangle-distinct graph has at least 16 vertices. -/
theorem regular_eight_triangle_distinct_card_ge_sixteen {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hreg : G.IsRegularOfDegree 8)
    (htd : simple_graph_is_triangle_distinct G) : 16 ≤ Fintype.card V := by
  by_contra h
  have h15 := regular_eight_triangle_distinct_card_ge_fifteen G hreg htd
  exact simple_graph_eight_regular_not_card_fifteen G (by omega) hreg htd
