import AFTD.Prelude

/-!
# digraph_six_circulant

Topic: graphs   Node: ca9a8ba1c1c2

Provenance: helper lemma. step towards digraph_ckk_subdivision_three_exceptional

The digraph on Fin 6 whose arcs are i → i+1 (indices mod 6) together with the chords 0 → 3, 1 → 4, 2 → 5.
-/

/-- The six-vertex digraph with arcs i → i+1 (cyclically) plus the chords 0 → 3, 1 → 4, 2 → 5: digirth 4, exactly three vertices of out-degree one. -/
def digraph_six_circulant : Digraph (Fin 6) where
  Adj x y := y = x + 1 ∨ (x.val < 3 ∧ y = x + 3)
