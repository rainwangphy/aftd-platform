import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphFaceVerts

/-!
# simple_graph_face_sum

Topic: combinatorics   Node: d2df0abfce9d

Provenance: formalization of a published result. Source: arXiv:2611.18384 Sec. 2.1, Eq. (1.1)

Given a simple graph G on Fin n with decidable adjacency, a permutation σ of G.Dart, a vertex weighting c : Fin n → ℕ, and a dart d : G.Dart, simple_graph_face_sum G σ c d is the sum of c v over all vertices v in simple_graph_face_verts G σ d.
-/

/-- The facial sum of the face containing dart d under vertex weighting c. -/
def simple_graph_face_sum {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) (c : Fin n → ℕ) (d : G.Dart) : ℕ := ∑ v ∈ simple_graph_face_verts G σ d, c v
