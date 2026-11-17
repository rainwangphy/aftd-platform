import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFaceVerts

/-!
# simple_graph_face_sum_real

Topic: combinatorics   Node: 7e9fd1a50459

Provenance: formalization of a published result. Source: arXiv:2611.18384 Definition 2.1

Given a simple graph G on Fin n with decidable adjacency, a permutation σ of G.Dart, a real vertex labeling c : Fin n → ℝ, and a dart d : G.Dart, simple_graph_face_sum_real G σ c d is the sum of c v over all vertices v in simple_graph_face_verts G σ d.
-/

/-- The facial sum of real vertex labels on the face bounded by dart d. -/
def simple_graph_face_sum_real {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) (c : Fin n → ℝ) (d : G.Dart) : ℝ := ∑ v ∈ simple_graph_face_verts G σ d, c v
