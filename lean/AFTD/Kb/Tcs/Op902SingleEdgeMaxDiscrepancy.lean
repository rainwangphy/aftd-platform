import AFTD.Prelude
import AFTD.Kb.Tcs.CarpoolMaxDiscrepancy
import AFTD.Kb.Tcs.MaxVertexDiscrepancy
import AFTD.Kb.Tcs.CarpoolStep

/-!
# op_902_single_edge_max_discrepancy

Topic: online_algorithms   Node: 43e58db008dd

Provenance: formalization of a published result. Source: arXiv:2611.00388 Sec 1.1, Online carpooling against an oblivious adversary

On any single-edge carpooling instance with distinct endpoints, the maximum discrepancy under any orientation sign is at most 1.
-/

/-- Any orientation on a single edge has maximum discrepancy at most 1. -/
theorem op_902_single_edge_max_discrepancy (n : ℕ) (e : Fin n × Fin n) (he : e.1 ≠ e.2)
    (b : Bool) :
    carpool_max_discrepancy n [e] [b] ≤ 1 := by
  have _ := he
  have hd0 : max_vertex_discrepancy n (fun _ => 0) ≤ 1 := by
    unfold max_vertex_discrepancy
    apply Finset.sup_le
    intro v _
    norm_num
  have hd1 : max_vertex_discrepancy n (carpool_step n (fun _ => 0) e b) ≤ 1 := by
    unfold max_vertex_discrepancy
    apply Finset.sup_le
    intro v _
    unfold carpool_step
    dsimp
    split_ifs <;> norm_num
  change max (max 0 (max_vertex_discrepancy n (fun _ => 0)))
    (max_vertex_discrepancy n (carpool_step n (fun _ => 0) e b)) ≤ 1
  rw [max_le_iff, max_le_iff]
  exact ⟨⟨by norm_num, hd0⟩, hd1⟩
