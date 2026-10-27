import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRotationFacePerm
import AFTD.Kb.Tcs.PosetNonemptyOrderIsoOfCardOrderHomEqOfConnected

/-!
# simple_graph_rotation_face_count

Topic: graphs   Node: 305558b66a39

Provenance: formalization of a published result. Source: Faces of a rotation system (Mohar-Thomassen, Graphs on Surfaces, Sec. 3.2); arXiv:2610.25886 (Extremal arborescences in graph orientations)

For a finite simple graph G (explicit argument) and a permutation σ : Equiv.Perm G.Dart of its darts, the number of faces of σ is the number of cycles of the face permutation simple_graph_rotation_face_perm G σ, counting fixed points as cycles: the cardinality of the quotient of G.Dart by the relation 'in the same cycle of the face permutation'.
-/

open Classical in
/-- Number of faces of a rotation system: orbits of the face permutation. -/
noncomputable def simple_graph_rotation_face_count {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) : ℕ :=
  Fintype.card (Quotient (Equiv.Perm.SameCycle.setoid (simple_graph_rotation_face_perm G σ)))
