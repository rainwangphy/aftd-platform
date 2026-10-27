import AFTD.Prelude

/-!
# simple_graph_rotation_face_perm

Topic: graphs   Node: 673942d6be79

Provenance: formalization of a published result. Source: Face tracing for rotation systems (Mohar-Thomassen, Graphs on Surfaces, Sec. 3.2); arXiv:2610.25886 (Extremal arborescences in graph orientations)

For a simple graph G (explicit argument) and a rotation system given as a permutation σ : Equiv.Perm G.Dart of the darts of G, the face permutation is the permutation of the darts (an Equiv.Perm G.Dart, the product σ * reversal) that sends each dart d to σ(d.symm), where d.symm is d with its direction reversed.
-/

/-- Face-tracing permutation d ↦ σ (d.symm) of a rotation system. -/
def simple_graph_rotation_face_perm {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm G.Dart) :
    Equiv.Perm G.Dart :=
  σ * Function.Involutive.toPerm SimpleGraph.Dart.symm (fun d => d.symm_symm)
