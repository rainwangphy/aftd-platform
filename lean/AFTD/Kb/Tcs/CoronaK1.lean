import AFTD.Prelude

/-!
# corona_k1

Topic: graphs   Node: 44a11d23b4d7

Provenance: formalization of a published result. Source: arXiv:2610.36821 Section 5

The corona product G ⊙ K_1 of a graph G with K_1 is the graph on vertex set V ⊕ V where the first copy induces G, each vertex in the second copy is a leaf attached to its corresponding vertex in G, and there are no edges between leaves.
-/

/-- The corona product G ⊙ K_1 of a simple graph G with K_1, formed by attaching a pendant leaf to every vertex of G. -/
def corona_k1 {V : Type*} (G : SimpleGraph V) : SimpleGraph (Sum V V) := {
  Adj := fun x y =>
    match x, y with
    | Sum.inl u, Sum.inl v => G.Adj u v
    | Sum.inl u, Sum.inr v => u = v
    | Sum.inr u, Sum.inl v => u = v
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (u | u) (v | v) h
    · exact G.symm.symm _ _ h
    · exact h.symm
    · exact h.symm
    · contradiction⟩
  loopless := ⟨by
    rintro (u | u) h
    · exact G.loopless.irrefl u h
    · contradiction⟩
}
