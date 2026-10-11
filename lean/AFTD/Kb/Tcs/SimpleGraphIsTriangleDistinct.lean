import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTriangleDegree

/-!
# simple_graph_is_triangle_distinct

Topic: graphs   Node: aef0d75a8fba

Provenance: formalization of a published result. Source: arXiv:2610.08478 (Regular K_3-Irregular Graphs of Every Regularity at Least Nine), Sec. 1 (triangle-distinct, or K_3-irregular, graphs).

A graph is triangle-distinct (K_3-irregular) when its vertex triangle-degrees are pairwise distinct.
-/

def simple_graph_is_triangle_distinct {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  Function.Injective (simple_graph_triangle_degree G)
