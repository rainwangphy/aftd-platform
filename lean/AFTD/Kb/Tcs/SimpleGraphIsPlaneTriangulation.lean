import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFaceLength
import AFTD.Kb.Tcs.SimpleGraphThreeVertexConnected
import AFTD.Kb.Tcs.SimpleGraphIsPlaneRotationSystem

/-!
# simple_graph_is_plane_triangulation

Topic: combinatorics   Node: 7a55206078c5

Provenance: formalization of a published result. Source: arXiv:2611.18384 Section 2.2

A simple graph G on Fin n with decidable adjacency and dart permutation σ is a plane triangulation if G is 3-vertex-connected, σ is a plane rotation system for G, and every face has length 3.
-/

/-- A plane triangulation is a 3-vertex-connected plane graph where every face has length 3. -/
def simple_graph_is_plane_triangulation {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) : Prop :=
  simple_graph_three_vertex_connected G ∧
  simple_graph_is_plane_rotation_system G σ ∧
  ∀ d : G.Dart, simple_graph_face_length G σ d = 3
