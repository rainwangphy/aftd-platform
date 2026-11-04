import AFTD.Prelude
import AFTD.Kb.Tcs.FanoPlane

/-!
# is_fano_free

Topic: combinatorics   Node: 04ca1b955655

Provenance: formalization of a published result. Source: arXiv:2610.01084 Section 3

A hypergraph H (a Finset of finite subsets of V) is Fano-free if there does not exist an embedding f : Fin 7 ↪ V such that for every hyperedge e ∈ fano_plane, the mapped finset e.map f belongs to H.
-/

/-- A hypergraph H : Finset (Finset V) is Fano-free if it contains no embedded copy of the Fano plane fano_plane. -/
def is_fano_free {V : Type*} (H : Finset (Finset V)) : Prop :=
  ¬ ∃ f : Fin 7 ↪ V, ∀ e ∈ fano_plane, e.map f ∈ H
