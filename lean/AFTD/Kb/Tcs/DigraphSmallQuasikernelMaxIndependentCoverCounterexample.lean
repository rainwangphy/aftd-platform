import AFTD.Prelude

/-!
# digraph_small_quasikernel_max_independent_cover_counterexample

Topic: graphs   Node: 644c7ddb6306

Provenance: helper lemma. Explicit obstruction found in experiment 13993 while studying OP-337 and https://arxiv.org/abs/2610.23487.

In the displayed source-free oriented seven-vertex graph, the displayed four-vertex independent set is maximum, the graph has a quasi-kernel of size at most half its vertices, and no such small quasi-kernel has this independent set in its closed out-neighborhood.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in528_out (v : Fin 7) : Finset (Fin 7) :=
  if v = 0 then {2} else if v = 1 then {0} else
  if v = 2 then {5} else if v = 4 then {1,3,5} else
  if v = 5 then {0,1,6} else if v = 6 then {4} else ∅

def in528_independent (Q : Finset (Fin 7)) : Prop :=
  ∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in528_out u

def in528_qk (Q : Finset (Fin 7)) : Prop :=
  in528_independent Q ∧
  ∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in528_out u ∨ ∃ w, w ∈ in528_out u ∧ v ∈ in528_out w

def in528_covers (Q I : Finset (Fin 7)) : Prop :=
  ∀ i ∈ I, ∃ q ∈ Q, q = i ∨ i ∈ in528_out q

instance (Q : Finset (Fin 7)) : Decidable (in528_independent Q) := by
  unfold in528_independent
  infer_instance
instance (Q : Finset (Fin 7)) : Decidable (in528_qk Q) := by
  unfold in528_qk
  infer_instance
instance (Q I : Finset (Fin 7)) : Decidable (in528_covers Q I) := by
  unfold in528_covers
  infer_instance

theorem digraph_small_quasikernel_max_independent_cover_counterexample :
    (∀ v, v ∉ in528_out v) ∧
    (∀ v, ∃ u, v ∈ in528_out u) ∧
    (∀ u v, v ∈ in528_out u → u ∉ in528_out v) ∧
    let I : Finset (Fin 7) := {1,2,3,6}
    in528_independent I ∧
    (∀ J : Finset (Fin 7), in528_independent J → J.card ≤ I.card) ∧
    (∃ Q : Finset (Fin 7), in528_qk Q ∧ 2 * Q.card ≤ 7) ∧
    (∀ Q : Finset (Fin 7), in528_qk Q → 2 * Q.card ≤ 7 → ¬ in528_covers Q I) := by
  decide
