import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphPrism
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# op_300_prism_three_leap_group_eq_top

Topic: graphs   Node: 0b1d20251950

Provenance: formalization of a published result. Source: arXiv:2610.18463 Question 5.4

For n = 3, the triangular prism graph P₁ □ C₃ on 6 vertices has full leap group S₆.
-/

private instance op_300_prism_three_boxProd_decidableRel {α β : Type*}
    [DecidableEq α] [DecidableEq β] (G : SimpleGraph α) (H : SimpleGraph β)
    [DecidableRel G.Adj] [DecidableRel H.Adj] : DecidableRel (G □ H).Adj := by
  intro x y
  rw [SimpleGraph.boxProd_adj]
  infer_instance

/-- The triangular prism graph has full leap group S₆. -/
theorem op_300_prism_three_leap_group_eq_top :
    simple_graph_leap_group (simple_graph_prism 3) = ⊤ := by
  let v0 : Fin 2 × Fin 3 := (0, 0)
  let v1 : Fin 2 × Fin 3 := (0, 1)
  let v2 : Fin 2 × Fin 3 := (0, 2)
  let v3 : Fin 2 × Fin 3 := (1, 0)
  let v4 : Fin 2 × Fin 3 := (1, 1)
  let v5 : Fin 2 × Fin 3 := (1, 2)
  let H2 : Equiv.Perm (Fin 2 × Fin 3) := List.formPerm [v0, v1, v2] * List.formPerm [v3, v5, v4]
  let H3 : Equiv.Perm (Fin 2 × Fin 3) := List.formPerm [v0, v1, v2, v5, v4, v3]
  let H10 : Equiv.Perm (Fin 2 × Fin 3) := List.formPerm [v0, v2, v1, v4, v5, v3]
  have m2 : H2 ∈ simple_graph_leap_group (simple_graph_prism 3) :=
    Subgroup.subset_closure (show simple_graph_is_hop _ H2 by
      unfold simple_graph_prism simple_graph_is_hop H2; decide)
  have m3 : H3 ∈ simple_graph_leap_group (simple_graph_prism 3) :=
    Subgroup.subset_closure (show simple_graph_is_hop _ H3 by
      unfold simple_graph_prism simple_graph_is_hop H3; decide)
  have m10 : H10 ∈ simple_graph_leap_group (simple_graph_prism 3) :=
    Subgroup.subset_closure (show simple_graph_is_hop _ H10 by
      unfold simple_graph_prism simple_graph_is_hop H10; decide)
  have hτ : H2 * H3 * H2 = Equiv.swap v1 v4 := by
    decide +kernel
  have mτ : Equiv.swap v1 v4 ∈ simple_graph_leap_group (simple_graph_prism 3) := by
    rw [← hτ]
    exact mul_mem (mul_mem m2 m3) m2
  have hcyc : H10.IsCycle :=
    List.isCycle_formPerm (by decide) (by decide)
  have hsupp : H10.support = ⊤ := by
    rw [List.support_formPerm_of_nodup _ (by decide) (by decide)]
    decide
  have h14 : H10 v1 = v4 := by decide
  rw [eq_top_iff, ← Equiv.Perm.closure_cycle_adjacent_swap hcyc hsupp v1, h14, Subgroup.closure_le]
  intro g hg
  rcases hg with rfl | rfl
  · exact m10
  · exact mτ
