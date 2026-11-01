import AFTD.Prelude

/-!
# plane_face_height_orientation

Topic: graphs   Node: e630e9a37e88

Provenance: helper lemma. step towards three_connected_plane_eulerian_non_alternating_exists_strictly_improving

The digraph induced by a height function y: the arc u → v is present exactly when the dart u → v has height exactly one more than the reverse dart v → u. Because the two heights of a dart and its reverse always differ by exactly 1, this puts exactly one direction on every edge of G.
-/

/-- The orientation of G induced by the height function y. -/
def plane_face_height_orientation {n : ℕ} (G : SimpleGraph (Fin n)) (y : G.Dart → ℤ) : Digraph (Fin n) := ⟨fun u v => ∃ h : G.Adj u v,
    y (SimpleGraph.Dart.mk (u, v) h) = y (SimpleGraph.Dart.mk (v, u) h.symm) + 1⟩
