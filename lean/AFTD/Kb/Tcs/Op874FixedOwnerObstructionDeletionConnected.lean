import AFTD.Prelude

/-!
# op874_fixed_owner_obstruction_deletion_connected

Topic: graphs   Node: 561cadf446b0

Provenance: helper lemma. Edge-deletion connectivity certificate for the fixed-owner obstruction to OP-874; experiment 43175.

In the explicit fourteen-vertex graph of the fixed-owner obstruction, deleting any one displayed edge leaves every pair of vertices connected by a path of displayed edges.
-/

namespace IN1258ConnectivityWitness
def in1258_left : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
def in1258_right : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
def in1258_edge (e : Fin 21) : Sym2 (Fin 14) := s(in1258_left e,in1258_right e)
def in1258_parent : Fin 21 → Fin 14 → Fin 14 := ![![0,4,7,10,11,6,9,0,4,2,0,7,9,11],![0,5,10,0,11,6,13,2,4,2,0,13,9,3],![0,4,7,0,11,6,13,0,4,2,3,7,9,3],![0,5,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,10,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,6,0,7,5,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,9,0,4,2,0,7,9,11],![0,4,7,0,11,6,13,0,12,2,0,7,9,3],![0,5,7,0,1,6,13,0,12,2,0,7,9,3],![0,4,7,0,11,12,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,9,0,4,2,0,7,9,3],![0,5,7,0,11,6,13,0,4,2,0,13,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3],![0,4,7,0,11,6,13,0,4,2,0,7,5,3],![0,4,7,0,11,6,13,0,4,2,0,7,9,3]]
def in1258_depth : Fin 21 → Fin 14 → Nat := ![![0,4,2,2,3,5,4,1,4,3,1,2,4,3],![0,5,2,1,4,4,3,3,5,3,1,3,4,2],![0,4,2,1,3,4,3,1,4,3,2,2,4,2],![0,5,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,4,1,2,5,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,5,4,1,4,3,1,2,4,3],![0,4,2,1,3,4,3,1,5,3,1,2,4,2],![0,5,2,1,6,4,3,1,5,3,1,2,4,2],![0,4,2,1,3,5,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,5,4,1,4,3,1,2,4,2],![0,5,2,1,4,4,3,1,5,3,1,3,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2],![0,4,2,1,3,4,3,1,4,3,1,2,5,2],![0,4,2,1,3,4,3,1,4,3,1,2,4,2]]
def in1258_adjAway (in1258_removed : Fin 21) (u v : Fin 14) : Prop :=
  ∃ e : Fin 21, e ≠ in1258_removed ∧ in1258_edge e = s(u,v)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem parent_step (in1258_removed : Fin 21) (v : Fin 14) (hv : v ≠ 0) :
    in1258_adjAway in1258_removed v (in1258_parent in1258_removed v) ∧ in1258_depth in1258_removed (in1258_parent in1258_removed v) < in1258_depth in1258_removed v := by
  revert v
  fin_cases in1258_removed <;> simp only [in1258_adjAway] <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem reaches_root (in1258_removed : Fin 21) (v : Fin 14) :
    Relation.ReflTransGen (in1258_adjAway in1258_removed) v 0 := by
  by_cases hv : v = 0
  · subst v
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.head (parent_step in1258_removed v hv).1
      (reaches_root in1258_removed (in1258_parent in1258_removed v))
termination_by in1258_depth in1258_removed v
decreasing_by exact (parent_step in1258_removed v hv).2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem connected_after_deletion (in1258_removed : Fin 21) (u v : Fin 14) :
    Relation.ReflTransGen (in1258_adjAway in1258_removed) u v := by
  have reverse : ∀ {a b}, Relation.ReflTransGen (in1258_adjAway in1258_removed) a b →
      Relation.ReflTransGen (in1258_adjAway in1258_removed) b a := by
    intro a b hp
    induction hp with
    | refl => exact Relation.ReflTransGen.refl
    | tail hp edge_step ih =>
      apply Relation.ReflTransGen.head _ ih
      rcases edge_step with ⟨e, he, hends⟩
      exact ⟨e, he, hends.trans Sym2.eq_swap⟩
  exact (reaches_root in1258_removed u).trans (reverse (reaches_root in1258_removed v))


end IN1258ConnectivityWitness

theorem op874_fixed_owner_obstruction_deletion_connected :
  let in1258_left : Fin 21 → Fin 14 := ![0,0,0,1,1,1,2,2,2,3,3,4,4,5,5,6,6,7,8,9,11]
  let in1258_right : Fin 21 → Fin 14 := ![3,7,10,4,5,8,7,9,10,10,13,8,11,6,12,9,13,11,12,12,13]
  let in1258_edge (e : Fin 21) : Sym2 (Fin 14) := s(in1258_left e,in1258_right e)
  let in1258_adjAway (in1258_removed : Fin 21) (u v : Fin 14) : Prop :=
    ∃ e : Fin 21, e ≠ in1258_removed ∧ in1258_edge e = s(u,v)
  ∀ in1258_removed : Fin 21, ∀ u v : Fin 14,
    Relation.ReflTransGen (in1258_adjAway in1258_removed) u v := by
  dsimp only
  intro in1258_removed u v
  exact IN1258ConnectivityWitness.connected_after_deletion in1258_removed u v
