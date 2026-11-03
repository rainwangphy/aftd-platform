import AFTD.Prelude

/-!
# categorical_prod

Topic: information   Node: dbae922a0f53

Provenance: formalization of a published result. Source: arXiv:2610.41977, Sec. 1

The categorical product of two simple graphs G and H has vertex set V(G) × V(H), with an edge between (u₁, v₁) and (u₂, v₂) if and only if u₁ is adjacent to u₂ in G and v₁ is adjacent to v₂ in H.
-/

/-- The categorical product (tensor product) of simple graphs: (u₁, v₁) is adjacent to (u₂, v₂) if and only if u₁ ~ u₂ in G and v₁ ~ v₂ in H. -/
def categorical_prod {V W : Type*} (G : SimpleGraph V) (H : SimpleGraph W) : SimpleGraph (V × W) := {
  Adj := fun x y => G.Adj x.1 y.1 ∧ H.Adj x.2 y.2
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => G.loopless.irrefl _ h.1⟩
}
