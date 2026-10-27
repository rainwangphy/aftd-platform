import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsRotationSystem
import AFTD.Kb.Tcs.SimpleGraphRotationFaceCount

/-!
# simple_graph_is_plane_rotation_system

Topic: graphs   Node: 3634c3114599

Provenance: formalization of a published result. Source: Genus-0 rotation systems = plane embeddings (rotation principle; Graphs on Surfaces, Thm 3.2.4 and Sec. 3.2); the fixed plane embedding of OP-541, arXiv:2610.25886 (Extremal arborescences in graph orientations)

For a finite simple graph G and a permutation σ : Equiv.Perm G.Dart of its darts, σ is a plane embedding of G given combinatorially, defined as the conjunction of three conditions: (1) G.Connected; (2) simple_graph_is_rotation_system G σ; and (3) genus 0, i.e. Euler's formula V - E + F = 2 computed in ℤ, with V = Fintype.card V, E = G.edgeFinset.card and F = simple_graph_rotation_face_count G σ. By the rotation principle for embeddings these are exactly the plane embeddings of a connected graph up to orientation-preserving homeomorphism (a graph with no edges has no darts, hence F = 0 here, so the one-vertex graph has none; this degenerate case does not arise for graphs with an edge).
-/

/-- σ is a plane embedding of the connected graph G: a rotation system with V - E + F = 2. -/
def simple_graph_is_plane_rotation_system {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) : Prop :=
  G.Connected ∧ simple_graph_is_rotation_system G σ ∧
    (Fintype.card V : ℤ) - (G.edgeFinset.card : ℤ) + (simple_graph_rotation_face_count G σ : ℤ) = 2
