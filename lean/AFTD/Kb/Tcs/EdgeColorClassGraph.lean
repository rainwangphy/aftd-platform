import AFTD.Prelude

/-!
# edge_color_class_graph

Topic: combinatorics   Node: b1841a8fe76c

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1259

For an arbitrary type V, given an edge coloring c : Sym2 V → Fin 5 and a color k : Fin 5, edge_color_class_graph c k is the simple graph on V where distinct vertices v, w : V are adjacent if and only if c(s(v, w)) = k.
-/

/-- The monochromatic subgraph for a given color under an edge coloring. -/
@[reducible] def edge_color_class_graph {V : Type*} (c : Sym2 V → Fin 5) (k : Fin 5) : SimpleGraph V where
  Adj v w := v ≠ w ∧ c s(v, w) = k
  symm := ⟨fun _ _ h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩
