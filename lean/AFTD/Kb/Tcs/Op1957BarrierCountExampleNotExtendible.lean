import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957BarrierCountExampleGraph
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound
import AFTD.Kb.Tcs.Op1957BarrierCountExampleForbidden

/-!
# op1957_barrier_count_example_not_extendible

Topic: graphs   Node: 6c564ca3c911

Provenance: helper lemma. OP-1957; explicit graph from the saturated barrier count model, experiments 39772, 39775 and 39778.

The explicit 44-vertex barrier count example is not 11-extendible.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

instance : DecidableRel op1957_barrier_count_example_forbidden := fun _ _ => by
  unfold op1957_barrier_count_example_forbidden
  infer_instance

instance : DecidableRel op1957_barrier_count_example_graph.Adj := fun u v => by
  change Decidable (u ≠ v ∧ ¬ op1957_barrier_count_example_forbidden u v ∧ ¬ op1957_barrier_count_example_forbidden v u)
  infer_instance

def in1159_bad_R : Finset (Fin 44) :=
  {0,1,2,3,4,5,6,7,8,9,10,11,22,23,25,26,27,28,33,34,35,36}

def in1159_bad_S : Finset (Fin 44) := Finset.univ \ in1159_bad_R

def in1159_bad_U : Finset (Fin 44) := {5,6,7,8,9,10,11}
def in1159_bad_T : Finset (Fin 44) := {22,23,25,26,27,28}

def in1159_bad_mate : Fin 44 → Fin 44 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,43,42,41,40,39,38,37,32,31,30,22,23,29,
    25,26,27,28,24,21,20,19,33,34,35,36,18,17,16,15,14,13,12]

theorem op1957_barrier_count_example_not_extendible :
    ¬ is_k_extendable op1957_barrier_count_example_graph 11 := by
  classical
  intro hext
  let S := {v : Fin 44 | v ∈ in1159_bad_S}
  let f (v : S) : S := ⟨in1159_bad_mate v.val, by revert v; decide⟩
  have hi : Function.Involutive f := by intro v; revert v; decide
  have ha : ∀ v : S, (op1957_barrier_count_example_graph.induce S).Adj v (f v) := by
    intro v; revert v; decide
  have hS : ∃ P : (op1957_barrier_count_example_graph.induce S).Subgraph, P.IsPerfectMatching :=
    perfect_matching_of_adjacency_involution _ f hi ha
  have hsize : S.ncard = 2*11 := by
    change (in1159_bad_S : Set (Fin 44)).ncard = 2*11
    rw [Set.ncard_coe_finset]
    decide
  have hcomp : Sᶜ = {v : Fin 44 | v ∈ in1159_bad_R} := by
    ext v
    simp [S,in1159_bad_S]
  have hR := extendible_matchable_two_k_vertices_complement_matchable op1957_barrier_count_example_graph 11 hext S hsize hS
  rw [hcomp] at hR
  have hU : in1159_bad_U ⊆ in1159_bad_R := by decide
  have hcover : ∀ u ∈ in1159_bad_U, ∀ v ∈ in1159_bad_R,
      op1957_barrier_count_example_graph.Adj u v → v ∈ in1159_bad_T := by decide
  have hb := induced_perfect_matching_neighbors_card_bound op1957_barrier_count_example_graph in1159_bad_R
    in1159_bad_U in1159_bad_T hU hcover hR
  have hn : ¬ in1159_bad_U.card ≤ in1159_bad_T.card := by decide
  exact hn hb
