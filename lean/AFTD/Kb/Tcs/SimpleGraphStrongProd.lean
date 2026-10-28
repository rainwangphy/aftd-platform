import AFTD.Prelude

/-!
# simple_graph_strong_prod

Topic: combinatorics   Node: 5b19a49ad90c

Provenance: formalization of a published result. Source: G. Sabidussi, The strong product of graphs, Monatshefte für Mathematik 64 (1960), 336–340; W. Imrich and S. Klavžar, Product Graphs: Structure and Recognition, Wiley, 2000, Section 1.4

The strong product of two simple graphs G and H: vertices are pairs (u, v) in V(G) × V(H), and two distinct pairs (u, v) and (u', v') are adjacent if (u = u' or G.Adj u u') and (v = v' or H.Adj v v').
-/

/-- The strong product G ⊠ H of simple graphs G and H. -/
def simple_graph_strong_prod {α β : Type*} (G : SimpleGraph α) (H : SimpleGraph β) :
    SimpleGraph (α × β) where
  Adj x y := x ≠ y ∧ (x.1 = y.1 ∨ G.Adj x.1 y.1) ∧ (x.2 = y.2 ∨ H.Adj x.2 y.2)
  symm := ⟨fun {_ _} h => ⟨h.1.symm,
    h.2.1.elim (fun h1 => Or.inl h1.symm) (fun h1 => Or.inr (G.adj_symm h1)),
    h.2.2.elim (fun h2 => Or.inl h2.symm) (fun h2 => Or.inr (H.adj_symm h2))⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
