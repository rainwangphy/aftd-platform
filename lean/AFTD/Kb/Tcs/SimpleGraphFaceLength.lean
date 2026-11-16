import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm

/-!
# simple_graph_face_length

Topic: combinatorics   Node: b4abd6057fac

Provenance: formalization of a published result. Source: arXiv:2611.18384 Sec. 1.2

Given a simple graph G on Fin n with decidable adjacency, a permutation σ of G.Dart, and a dart d : G.Dart, simple_graph_face_length G σ d is the cardinality (as a natural number) of the Finset of darts in G.Dart that belong to the same cycle as d under simple_graph_rotation_face_perm G σ.
-/

/-- The length of the face containing dart d in rotation system σ. -/
def simple_graph_face_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (σ : Equiv.Perm G.Dart) (d : G.Dart) : ℕ := (Finset.univ.filter (fun d' => (simple_graph_rotation_face_perm G σ).SameCycle d d')).card
