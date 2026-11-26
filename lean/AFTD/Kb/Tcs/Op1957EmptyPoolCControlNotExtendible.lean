import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957EmptyPoolControlGraph
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.Op1957EmptyPoolControlForbidden

/-!
# op1957_empty_pool_c_control_not_extendible

Topic: graphs   Node: dd74a5acf57c

Provenance: helper lemma. OP-1957; explicit exceptional empty-pool controls, experiments 41527, 41538 and 41541.

The explicit control with z=17 is not 7-extendible.
-/

instance (z : Fin 28) : DecidableRel (op1957_empty_pool_control_graph z).Adj := fun _ _ => by
  unfold op1957_empty_pool_control_graph op1957_empty_pool_control_forbidden
  infer_instance

private def in1214_control_S : Finset (Fin 28) := {1,2,3,4,5,6,7,8,9,10,11,12,13,20}
private def in1214_control_R : Finset (Fin 28) := Finset.univ \ in1214_control_S
private def in1214_control_U : Finset (Fin 28) := {14,15,16,17}
private def in1214_control_T : Finset (Fin 28) := {0,18,19}
private def in1214_control_mate : Fin 28 → Fin 28 :=
  ![0,2,1,4,3,13,12,11,10,20,8,7,6,5,14,15,16,17,18,19,9,21,22,23,24,25,26,27]

theorem op1957_empty_pool_c_control_not_extendible : ¬ is_k_extendable (op1957_empty_pool_control_graph 17) 7 := by
  set_option maxHeartbeats 4000000 in
    classical
    intro hext
    let S := {v : Fin 28 | v ∈ in1214_control_S}
    let f (v : S) : S := ⟨in1214_control_mate v.val, by revert v; decide⟩
    have hi : Function.Involutive f := by intro v; revert v; decide
    have ha : ∀ v : S, ((op1957_empty_pool_control_graph 17).induce S).Adj v (f v) := by
      intro v
      revert v
      decide
    have hS : ∃ P : ((op1957_empty_pool_control_graph 17).induce S).Subgraph, P.IsPerfectMatching :=
      perfect_matching_of_adjacency_involution _ f hi ha
    have hsize : S.ncard = 2*7 := by
      change (in1214_control_S : Set (Fin 28)).ncard = 2*7
      rw [Set.ncard_coe_finset]
      decide
    have hcomp : Sᶜ = {v : Fin 28 | v ∈ in1214_control_R} := by
      ext v
      simp [S,in1214_control_R]
    have hR := extendible_matchable_two_k_vertices_complement_matchable (op1957_empty_pool_control_graph 17) 7 hext S hsize hS
    rw [hcomp] at hR
    have hU : in1214_control_U ⊆ in1214_control_R := by decide
    have hcover : ∀ u ∈ in1214_control_U, ∀ v ∈ in1214_control_R,
        (op1957_empty_pool_control_graph 17).Adj u v → v ∈ in1214_control_T := by decide
    have hb := induced_perfect_matching_neighbors_card_bound (op1957_empty_pool_control_graph 17) in1214_control_R
      in1214_control_U in1214_control_T hU hcover hR
    have hn : ¬ in1214_control_U.card ≤ in1214_control_T.card := by decide
    exact hn hb
