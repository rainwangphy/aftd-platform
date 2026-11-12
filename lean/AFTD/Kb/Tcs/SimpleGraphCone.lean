import AFTD.Prelude

/-!
# simple_graph_cone

Topic: graphs   Node: cae1f6e31f03

Provenance: formalization of a published result. Source: arXiv:2611.13656 Section 1

The cone or graph join G ∨ K_1 of a simple graph G is the simple graph on Option V obtained by adding a universal vertex none adjacent to every vertex of G.
-/

/-- The cone graph G ∨ K_1 formed by adding a universal vertex none to G. -/
def simple_graph_cone {V : Type*} (G : SimpleGraph V) : SimpleGraph (Option V) where
  Adj
    | some u, some v => G.Adj u v
    | none, some _ => True
    | some _, none => True
    | none, none => False
  symm := ⟨by
    rintro (_ | u) (_ | v) h <;> try trivial
    exact G.adj_symm h⟩
  loopless := ⟨by
    rintro (_ | u) h
    · exact h
    · exact G.loopless.irrefl u h⟩
