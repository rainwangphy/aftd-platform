import AFTD.Prelude

/-!
# add_apex_edges

Topic: communication   Node: 792b6fc9cadc

Provenance: original. Related work: arXiv:2611.06626

Given a graph G on vertex type V and a subset of vertices T ⊆ V, add_apex_edges G T is the simple graph on Option V whose vertices are V ∪ {none}, retaining all edges of G on V and having edges between none and each vertex in T.
-/

/-- Graph on Option V extending G by an apex vertex adjacent to the vertices in T. -/
def add_apex_edges {V : Type*} (G : SimpleGraph V) (T : Set V) : SimpleGraph (Option V) := {
  Adj := fun x y =>
    match x, y with
    | some u, some v => G.Adj u v
    | none, some t => t ∈ T
    | some t, none => t ∈ T
    | none, none => False
  symm := ⟨by rintro (u | _) (v | _) h <;> simp_all [G.adj_symm]⟩
  loopless := ⟨by rintro (u | _) h <;> simp_all⟩
}
