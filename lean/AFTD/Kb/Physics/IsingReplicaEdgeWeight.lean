import AFTD.Prelude

/-!
# ising_replica_edge_weight

Topic: quantum_mechanics   Node: ead8d0a01029

Provenance: helper lemma. step towards ising_graph_state_four_replica_sum_eq_sixteen_spin_partition_fn

For a real angle θ and a difference pattern d : Fin 4 → Fin 2 (component 0 records whether the two endpoints agree in the a-replica, components 1,2,3 in the replicas x1,x2,x3; value 0 means agree), the per-edge weight of the four-replica product is exp(i θ (1-δ)(s₁-s₂+s₃-s₁s₂s₃)), where δ and s₁,s₂,s₃ are +1 exactly when the corresponding difference bit is 0.
-/

open scoped BigOperators Classical in
/-- Per-edge complex weight exp(i θ (1-δ)(s₁-s₂+s₃-s₁s₂s₃)) of the four-replica sum, indexed by the four difference bits. -/
noncomputable def ising_replica_edge_weight (θ : ℝ) (d : Fin 4 → Fin 2) : ℂ := Complex.exp (Complex.I * ((θ : ℂ) * ((1 - (if d 0 = 0 then (1:ℝ) else -1)) *
    ((if d 1 = 0 then (1:ℝ) else -1) - (if d 2 = 0 then (1:ℝ) else -1) +
      (if d 3 = 0 then (1:ℝ) else -1) - (if d 1 = 0 then (1:ℝ) else -1) *
        (if d 2 = 0 then (1:ℝ) else -1) * (if d 3 = 0 then (1:ℝ) else -1)))))
