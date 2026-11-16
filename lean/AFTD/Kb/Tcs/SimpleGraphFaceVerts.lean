import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm

/-!
# simple_graph_face_verts

Topic: combinatorics   Node: 8c1a075b6aa9

Provenance: formalization of a published result. Source: arXiv:2611.18384 Sec. 2.1

Given a simple graph G on Fin n with decidable adjacency, a permutation σ of G.Dart, and a dart d : G.Dart, simple_graph_face_verts G σ d is the Finset of vertices in Fin n defined as the image under (fun d' => d'.fst) of the Finset of darts in the same cycle as d under simple_graph_rotation_face_perm G σ.
-/

/-- The set of vertices incident to the face containing dart d in rotation system σ. -/
def simple_graph_face_verts {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) (d : G.Dart) : Finset (Fin n) := (Finset.univ.filter (fun d' => (simple_graph_rotation_face_perm G σ).SameCycle d d')).image (fun d' => d'.fst)
