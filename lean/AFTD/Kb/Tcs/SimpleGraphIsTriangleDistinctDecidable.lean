import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree
import AFTD.Kb.Tcs.SimpleGraphIsTriangleDistinct

/-!
# simple_graph_is_triangle_distinct_decidable

Topic: graphs   Node: b6450f0432ca

Provenance: helper lemma. step towards exists_nonempty_regular_eight_triangle_distinct

For a finite graph, the proposition that the vertex triangle-degrees are pairwise distinct is decidable.
-/

/-- Triangle-distinctness of a graph on a finite vertex type is decidable. -/
instance simple_graph_is_triangle_distinct_decidable {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Decidable (simple_graph_is_triangle_distinct G) := inferInstanceAs (Decidable (Function.Injective (fun v => simple_graph_triangle_degree G v)))
