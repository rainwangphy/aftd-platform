import AFTD.Prelude

/-!
# is_connected_vertex_set

Topic: fair_division   Node: 206cc266f7f4

A vertex set S of a graph G is connected if the subgraph of G induced by S is connected (in particular S is nonempty).
-/

/-- `S` induces a connected subgraph of `G` (connectedness includes nonemptiness). -/
def is_connected_vertex_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop :=
  (G.induce S).Connected
