import AFTD.Prelude

/-!
# dist_two_graph

Topic: graphs   Node: 7ba183845fe5

Provenance: helper lemma. step towards sparse_strong_odd_five_list_coloring

The graph on V in which two distinct vertices are adjacent when they are adjacent in G or have a common neighbour in G; its neighbour sets are the sets of vertices at distance 1 or 2 in G.
-/

/-- The distance-≤2 graph (square) of `G`: `a` and `b` are adjacent when they are distinct and joined by a walk of length 1 or 2 in `G`. A proper colouring of this graph assigns distinct colours to any two neighbours of a common vertex, which is exactly what a strong odd colouring of `G` needs. -/
@[reducible] def dist_two_graph {V : Type} (G : SimpleGraph V) : SimpleGraph V := SimpleGraph.fromRel fun a b => G.Adj a b ∨ ∃ c, G.Adj a c ∧ G.Adj c b
