import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm

/-!
# plane_face_height

Topic: graphs   Node: 17e69eafabe0

Provenance: helper lemma. step towards three_connected_plane_eulerian_non_alternating_exists_strictly_improving

A height function for the rotation system σ is a function y from the darts of G to ℤ that is constant on the cycles of the face permutation (so it is really a labelling of the faces of σ) and satisfies y d = y d.symm + 1 or y d = y d.symm - 1 for every dart d: the two sides of an edge have heights differing by exactly 1.
-/

/-- A height function on the darts of G for the rotation system σ: constant on σ-faces, changing by exactly 1 across every edge. -/
def plane_face_height {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm G.Dart) (y : G.Dart → ℤ) : Prop := (∀ d : G.Dart, y (simple_graph_rotation_face_perm G σ d) = y d) ∧
    ∀ d : G.Dart, y d = y d.symm + 1 ∨ y d = y d.symm - 1
