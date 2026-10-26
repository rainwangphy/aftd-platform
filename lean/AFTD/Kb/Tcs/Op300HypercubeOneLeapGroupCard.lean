import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHypercube
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphHypercubeCoordinateFlip
import AFTD.Kb.Tcs.SimpleGraphIsHopMemLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# op_300_hypercube_one_leap_group_card

Topic: graphs   Node: d343abd12b19

Provenance: formalization of a published result. Source: arXiv:2610.18463 Question 5.4

The hypercube graph Q₁ (the path K₂) has leap group of cardinality 2.
-/

/-- The 1-dimensional hypercube has leap group of order 2. -/
theorem op_300_hypercube_one_leap_group_card :
    Nat.card (simple_graph_leap_group (simple_graph_hypercube 1)) = 2 := by
  have htop : simple_graph_leap_group (simple_graph_hypercube 1) = ⊤ := by
    have hflip_hop : simple_graph_is_hop (simple_graph_hypercube 1) (simple_graph_hypercube_coordinate_flip 1 0) := by
      intro v
      rw [simple_graph_hypercube, SimpleGraph.fromRel_adj]
      refine ⟨?_, ?_⟩
      · intro h
        apply_fun (· 0) at h
        change v 0 = Function.update v 0 (!v 0) 0 at h
        simp at h
      · left
        refine ⟨0, ?_, ?_⟩
        · change v 0 ≠ Function.update v 0 (!v 0) 0
          simp
        · intro j hj
          fin_cases j
          rfl
    have hflip_mem : simple_graph_hypercube_coordinate_flip 1 0 ∈ simple_graph_leap_group (simple_graph_hypercube 1) :=
      simple_graph_is_hop_mem_leap_group _ _ hflip_hop
    rw [Subgroup.eq_top_iff']
    intro σ
    have hcases : σ = 1 ∨ σ = simple_graph_hypercube_coordinate_flip 1 0 := by
      revert σ
      decide
    rcases hcases with rfl | rfl
    · exact Subgroup.one_mem _
    · exact hflip_mem
  rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide
