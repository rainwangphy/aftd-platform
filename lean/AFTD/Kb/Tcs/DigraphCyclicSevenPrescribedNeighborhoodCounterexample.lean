import AFTD.Prelude

/-!
# digraph_cyclic_seven_prescribed_neighborhood_counterexample

Topic: graphs   Node: 911ab4a3631e

Provenance: helper lemma. Explicit finite counterexample discovered and audited in the cited computations; no novelty is claimed.

The displayed eight-vertex graph contains the cyclic seven-tournament, but no quasi-kernel covers the closed out-neighborhood of vertex 0 within that tournament.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in541_forced_parent_out (v : Fin 8) : Finset (Fin 8) :=
  if v = 0 then {1,2,4} else if v = 1 then {2,3,5} else
  if v = 2 then {3,4,6} else if v = 3 then {0,4,5} else
  if v = 4 then {1,5,6} else if v = 5 then {0,2,6} else
  if v = 6 then {0,1,3} else {0}

def in541_forced_parent_qk (Q : Finset (Fin 8)) : Prop :=
  (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in541_forced_parent_out u) ∧
  (∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in541_forced_parent_out u ∨
    ∃ w, w ∈ in541_forced_parent_out u ∧ v ∈ in541_forced_parent_out w)

instance (Q : Finset (Fin 8)) : Decidable (in541_forced_parent_qk Q) := by
  unfold in541_forced_parent_qk
  infer_instance

theorem digraph_cyclic_seven_prescribed_neighborhood_counterexample :
    (∀ v, v ∉ in541_forced_parent_out v) ∧
    (∀ u v : Fin 8, u.val < 7 → v.val < 7 →
      (v ∈ in541_forced_parent_out u ↔
        (v.val + 7 - u.val) % 7 ∈ ({1,2,4} : Finset ℕ))) ∧
    (∀ Q : Finset (Fin 8), in541_forced_parent_qk Q →
      ¬ (∀ v ∈ ({0,1,2,4} : Finset (Fin 8)),
        ∃ q ∈ Q, q = v ∨ v ∈ in541_forced_parent_out q)) := by
  decide
