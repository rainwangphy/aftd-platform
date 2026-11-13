import AFTD.Prelude
import AFTD.Kb.Tcs.DirectedMultigraph

/-!
# IsDirectedWalk

Topic: graphs   Node: a1187692f44a

Provenance: formalization of a published result. Source: arXiv:2611.12330 Section 2

An inductive predicate IsDirectedWalk G u w p stating that a list of edges p : List E forms a directed walk from vertex u to vertex w in the directed multigraph G.
-/

/-- Inductive predicate for a directed walk in a directed multigraph. -/
inductive IsDirectedWalk {V E : Type*} (G : DirectedMultigraph V E) : V → V → List E → Prop | nil (v : V) : IsDirectedWalk G v v []
  | cons {u v w : V} (e : E) (p : List E)
      (he_src : G.src e = u) (he_tgt : G.tgt e = v)
      (hp : IsDirectedWalk G v w p) : IsDirectedWalk G u w (e :: p)
