import AFTD.Prelude

/-!
# op309_pendant_star_forces_six_clique

Topic: graphs   Node: b89345404632

Provenance: helper lemma. Finite obstruction found in experiments 30942, 30943, and 30947.

Every total edge-dominating star-forest witness in the six-vertex pendant graph has a six-clique in its conflict graph.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 1000000

def op309_pendant_edges : Fin 8 → Fin 6 × Fin 6 :=
  ![(0,1), (0,2), (0,4), (1,3), (1,5), (2,3), (2,5), (3,5)]

def op309_pendant_meets (i : Fin 8) (v : Fin 6) : Prop :=
  (op309_pendant_edges i).1 = v ∨ (op309_pendant_edges i).2 = v

instance (i : Fin 8) (v : Fin 6) : Decidable (op309_pendant_meets i v) := by
  unfold op309_pendant_meets
  infer_instance

def op309_pendant_adj (i j : Fin 8) : Prop :=
  i ≠ j ∧ ∃ v : Fin 6, op309_pendant_meets i v ∧ op309_pendant_meets j v

instance : DecidableRel op309_pendant_adj := fun i j => by
  unfold op309_pendant_adj
  infer_instance

def op309_pendant_witness_adj (R : Finset (Fin 8)) (i j : Fin 8) : Prop :=
  i ≠ j ∧ (op309_pendant_adj i j ∨
    ∃ r ∈ R, op309_pendant_adj r i ∧ op309_pendant_adj r j)

instance (R : Finset (Fin 8)) : DecidableRel (op309_pendant_witness_adj R) :=
  fun i j => by unfold op309_pendant_witness_adj; infer_instance

def op309_pendant_total (R : Finset (Fin 8)) : Prop :=
  ∀ i : Fin 8, ∃ r ∈ R, op309_pendant_adj i r

instance (R : Finset (Fin 8)) : Decidable (op309_pendant_total R) := by
  unfold op309_pendant_total
  infer_instance

def op309_pendant_star (R : Finset (Fin 8)) : Prop :=
  ∀ i ∈ R, ∀ j ∈ R, ∀ k ∈ R,
    i ≠ j → j ≠ k → i ≠ k → op309_pendant_adj i j → op309_pendant_adj j k →
    ∃ v : Fin 6, op309_pendant_meets i v ∧ op309_pendant_meets j v ∧ op309_pendant_meets k v

instance (R : Finset (Fin 8)) : Decidable (op309_pendant_star R) := by
  unfold op309_pendant_star
  infer_instance

def op309_pendant_clique6 (R : Finset (Fin 8)) : Prop :=
  ∃ S : Finset (Fin 8), S.card = 6 ∧
    ∀ i ∈ S, ∀ j ∈ S, i ≠ j → op309_pendant_witness_adj R i j

instance (R : Finset (Fin 8)) : Decidable (op309_pendant_clique6 R) := by
  unfold op309_pendant_clique6
  infer_instance

theorem op309_pendant_star_forces_six_clique :
    ∀ R : Finset (Fin 8), op309_pendant_total R → op309_pendant_star R →
      op309_pendant_clique6 R := by
  decide
