import AFTD.Prelude
import AFTD.Kb.Tcs.C7BoxK3Distance
import AFTD.Kb.Tcs.CyclicDistanceSeven

/-!
# c7_box_k3_graph

Topic: graphs   Node: 41f8990ad9dc

Provenance: helper lemma. step towards not_forall_power_well_covered_diam_le_three_and_twin_free_bounded

The graph C_7 (box) C_3 = C_21(1,7) on Z/7 x {0,1,2}: u and v are adjacent iff they are distinct and c7_box_k3_distance u v = 1.
-/

/-- The box product `C_7 □ C_3` on `ZMod 7 × Fin 3`, equivalently the circulant `C_21(1,7)`. -/
def c7_box_k3_graph : SimpleGraph (ZMod 7 × Fin 3) where
  Adj u v := u ≠ v ∧ c7_box_k3_distance u v = 1
  symm := ⟨fun u v h => ⟨h.1.symm, by
    have hc : c7_box_k3_distance v u = c7_box_k3_distance u v := by
      simp only [c7_box_k3_distance, cyclic_distance_seven, min_comm, eq_comm]
    rw [hc]; exact h.2⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩
