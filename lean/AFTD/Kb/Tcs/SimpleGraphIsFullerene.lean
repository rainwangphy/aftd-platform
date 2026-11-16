import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphThreeVertexConnected
import AFTD.Kb.Tcs.SimpleGraphIsPlaneRotationSystem
import AFTD.Kb.Tcs.SimpleGraphFaceLength

/-!
# simple_graph_is_fullerene

Topic: combinatorics   Node: 2be0b60652d8

Provenance: formalization of a published result. Source: arXiv:2611.18384 Sec. 1.2, Sec. 5

A simple graph G on Fin n with decidable adjacency and dart permutation σ is a fullerene if G is 3-vertex-connected, every vertex of G has degree 3, σ is a plane rotation system for G, and every dart d has simple_graph_face_length G σ d equal to 5 or 6.
-/

/-- A fullerene is a 3-connected cubic plane graph with all face lengths 5 or 6. -/
def simple_graph_is_fullerene {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) : Prop :=
  simple_graph_three_vertex_connected G ∧
  (∀ v : Fin n, G.degree v = 3) ∧
  simple_graph_is_plane_rotation_system G σ ∧
  ∀ d : G.Dart, simple_graph_face_length G σ d = 5 ∨ simple_graph_face_length G σ d = 6
