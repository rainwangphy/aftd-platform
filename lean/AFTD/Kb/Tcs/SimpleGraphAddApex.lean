import AFTD.Prelude

/-!
# simple_graph_add_apex

Topic: communication   Node: dd16f6d983db

Provenance: original. Related work: arXiv:2611.06626 Section 2.4

Given a simple graph G on vertex type V and a set of vertices S ⊆ V, simple_graph_add_apex G S is the simple graph on Option V obtained by adjoining a new apex vertex (none) that is adjacent precisely to the vertices some v for v ∈ S, while preserving all edges of G on the original vertices.
-/

/-- Add an apex vertex (none) connected to vertices in S to a simple graph G on V. -/
def simple_graph_add_apex {V : Type*} (G : SimpleGraph V) (S : Set V) : SimpleGraph (Option V) :=
  SimpleGraph.fromRel fun
    | some u, some v => G.Adj u v
    | none, some v => v ∈ S
    | some u, none => u ∈ S
    | none, none => False
