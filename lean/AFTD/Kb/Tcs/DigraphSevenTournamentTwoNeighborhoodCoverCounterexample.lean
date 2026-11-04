import AFTD.Prelude

/-!
# digraph_seven_tournament_two_neighborhood_cover_counterexample

Topic: graphs   Node: dbadd2c9847f

Provenance: helper lemma. Classical cyclic tournament, https://www.combinatorics.org/ojs/index.php/eljc/article/download/v13i1r69/pdf/; the two-cover obstruction was audited in experiment 13998.

The displayed source-free seven-vertex tournament has all singleton quasi-kernels, every quasi-kernel is a singleton, no pair of their closed out-neighborhoods covers all vertices, and each vertex belongs to four of those neighborhoods.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in528_tournament_out (v : Fin 7) : Finset (Fin 7) :=
  if v = 0 then {1,2,4} else if v = 1 then {2,3,5} else
  if v = 2 then {3,4,6} else if v = 3 then {0,4,5} else
  if v = 4 then {1,5,6} else if v = 5 then {0,2,6} else {0,1,3}

def in528_tournament_qk (Q : Finset (Fin 7)) : Prop :=
  (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in528_tournament_out u) ∧
  (∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in528_tournament_out u ∨
    ∃ w, w ∈ in528_tournament_out u ∧ v ∈ in528_tournament_out w)
instance (Q : Finset (Fin 7)) : Decidable (in528_tournament_qk Q) := by
  unfold in528_tournament_qk
  infer_instance

theorem digraph_seven_tournament_two_neighborhood_cover_counterexample :
    (∀ v, v ∉ in528_tournament_out v) ∧
    (∀ v, ∃ u, v ∈ in528_tournament_out u) ∧
    (∀ u v, u ≠ v → (v ∈ in528_tournament_out u ∨ u ∈ in528_tournament_out v)) ∧
    (∀ v, in528_tournament_qk {v}) ∧
    (∀ Q : Finset (Fin 7), in528_tournament_qk Q → ∃ v, Q = {v}) ∧
    (∀ u v : Fin 7, ∃ z : Fin 7,
      z ≠ u ∧ z ∉ in528_tournament_out u ∧ z ≠ v ∧ z ∉ in528_tournament_out v) ∧
    (∀ z : Fin 7,
      (Finset.univ.filter fun u => u = z ∨ z ∈ in528_tournament_out u).card = 4) := by
  decide
