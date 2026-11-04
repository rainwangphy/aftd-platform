import AFTD.Prelude

/-!
# digraph_seven_pair_four_cover_counterexample

Topic: graphs   Node: 370d12b84119

Provenance: helper lemma. Explicit finite counterexample discovered and audited in the cited computations; no novelty is claimed.

The displayed source-free oriented seven-vertex graph has no quasi-kernel whose closed out-neighborhood contains both vertices 0 and 1 and at least four vertices.
-/

set_option maxRecDepth 50000
set_option maxHeartbeats 50000000

def in541_pair_four_out (v : Fin 7) : Finset (Fin 7) :=
  if v = 0 then {2,4,5,6} else if v = 1 then {0,3} else
  if v = 2 then {1} else if v = 3 then {6} else
  if v = 4 then {1,3,5} else if v = 5 then {1,6} else {1,2}

def in541_pair_four_qk (Q : Finset (Fin 7)) : Prop :=
  (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → v ∉ in541_pair_four_out u) ∧
  (∀ v, ∃ u ∈ Q, u = v ∨ v ∈ in541_pair_four_out u ∨
    ∃ w, w ∈ in541_pair_four_out u ∧ v ∈ in541_pair_four_out w)

instance (Q : Finset (Fin 7)) : Decidable (in541_pair_four_qk Q) := by
  unfold in541_pair_four_qk
  infer_instance

theorem digraph_seven_pair_four_cover_counterexample :
    (∀ v, v ∉ in541_pair_four_out v) ∧
    (∀ v, ∃ u, v ∈ in541_pair_four_out u) ∧
    (∀ u v, v ∈ in541_pair_four_out u → u ∉ in541_pair_four_out v) ∧
    (∀ Q : Finset (Fin 7), in541_pair_four_qk Q →
      (∃ q ∈ Q, q = 0 ∨ (0 : Fin 7) ∈ in541_pair_four_out q) →
      (∃ q ∈ Q, q = 1 ∨ (1 : Fin 7) ∈ in541_pair_four_out q) →
      (Finset.univ.filter fun v => ∃ q ∈ Q,
        q = v ∨ v ∈ in541_pair_four_out q).card < 4) := by
  decide
