import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957EmptyPoolControlGraph
import AFTD.Kb.Tcs.Op1957EmptyPoolControlForbidden
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.IsKExtendable

/-!
# op1957_empty_pool_control_delete_0_16_not_extendible

Topic: graphs   Node: ac9664965b37

Provenance: helper lemma. OP-1957 exceptional 28-vertex positive-barrier control, explicit matching and residual obstruction in experiments 41834 and 41836.

Deleting edge {0,16} from the displayed 28-vertex control with parameter 5 yields a graph that is not 7-extendible.
-/

set_option maxHeartbeats 4000000
local instance  aftdLocal_fc7f15aa39c566db_0 (z : Fin 28) : DecidableRel (op1957_empty_pool_control_graph z).Adj := fun _ _ => by
  unfold op1957_empty_pool_control_graph op1957_empty_pool_control_forbidden
  infer_instance

private def controlH : SimpleGraph (Fin 28) :=
  (op1957_empty_pool_control_graph 5).deleteEdges {s((0 : Fin 28), (16 : Fin 28))}
local instance  aftdLocal_fc7f15aa39c566db_1 : DecidableRel controlH.Adj := by
  unfold controlH
  infer_instance
private def controlS : Finset (Fin 28) := {1,2,3,4,6,7,8,9,10,11,12,13,19,20}
private def controlR : Finset (Fin 28) := Finset.univ \ controlS
private def controlU : Finset (Fin 28) := {14,15,16}
private def controlT : Finset (Fin 28) := {17,18}
private def controlMate : Fin 28 → Fin 28 :=
  ![0,2,1,4,3,5,7,6,9,8,11,10,13,12,14,15,16,17,18,20,19,21,22,23,24,25,26,27]

theorem op1957_empty_pool_control_delete_0_16_not_extendible :
    ¬ is_k_extendable ((op1957_empty_pool_control_graph 5).deleteEdges {s((0 : Fin 28), (16 : Fin 28))}) 7 := by
  classical
  intro hext
  let S := {v : Fin 28 | v ∈ controlS}
  let f (v : S) : S := ⟨controlMate v.val, by revert v; decide⟩
  have hi : Function.Involutive f := by intro v; revert v; decide
  have ha : ∀ v : S, (controlH.induce S).Adj v (f v) := by
    intro v
    revert v
    decide
  have hS : ∃ P : (controlH.induce S).Subgraph, P.IsPerfectMatching :=
    perfect_matching_of_adjacency_involution _ f hi ha
  have hsize : S.ncard = 2*7 := by
    change (controlS : Set (Fin 28)).ncard = 2*7
    rw [Set.ncard_coe_finset]
    decide
  have hcomp : Sᶜ = {v : Fin 28 | v ∈ controlR} := by
    ext v
    simp [S,controlR]
  have hR := extendible_matchable_two_k_vertices_complement_matchable controlH 7 hext S hsize hS
  rw [hcomp] at hR
  have hU : controlU ⊆ controlR := by decide
  have hcover : ∀ u ∈ controlU, ∀ v ∈ controlR, controlH.Adj u v → v ∈ controlT := by decide
  have hb := induced_perfect_matching_neighbors_card_bound controlH controlR controlU controlT hU hcover hR
  have hn : ¬ controlU.card ≤ controlT.card := by decide
  exact hn hb
