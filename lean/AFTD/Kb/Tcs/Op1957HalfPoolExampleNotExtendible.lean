import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957HalfPoolExampleGraph
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.InducedPerfectMatchingNeighborsCardBound
import AFTD.Kb.Tcs.Op1957HalfPoolExampleForbidden

/-!
# op1957_half_pool_example_not_extendible

Topic: graphs   Node: dea48e273501

Provenance: helper lemma. OP-1957; explicit 52-vertex half-pool graph, experiments 39914, 39920, and 39925.

The explicit 52-vertex half-pool example is not 13-extendible.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

instance : DecidableRel op1957_half_pool_example_forbidden := fun _ _ => by unfold op1957_half_pool_example_forbidden; infer_instance

instance : DecidableRel op1957_half_pool_example_graph.Adj := fun u v => by
  change Decidable (u ≠ v ∧ ¬ op1957_half_pool_example_forbidden u v ∧ ¬ op1957_half_pool_example_forbidden v u)
  infer_instance

def in1159_half_R : Finset (Fin 52) :=
  {0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,26,27,28,39,40,41}
def in1159_half_S : Finset (Fin 52) := Finset.univ \ in1159_half_R
def in1159_half_U : Finset (Fin 52) := {12,13,14,15,16,17}
def in1159_half_T : Finset (Fin 52) := {18,19}

def in1159_half_mate : Fin 52 → Fin 52 :=
  ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,21,20,23,22,25,24,26,27,28,30,29,32,31,34,33,36,35,38,37,39,40,41,43,42,45,44,47,46,49,48,51,50]

theorem op1957_half_pool_example_not_extendible : ¬ is_k_extendable op1957_half_pool_example_graph 13 := by
  classical
  intro hext
  let S := {v : Fin 52 | v ∈ in1159_half_S}
  let f (v : S) : S := ⟨in1159_half_mate v.val, by revert v; decide⟩
  have hi : Function.Involutive f := by intro v; revert v; decide
  have ha : ∀ v : S, (op1957_half_pool_example_graph.induce S).Adj v (f v) := by intro v; revert v; decide
  have hS : ∃ P : (op1957_half_pool_example_graph.induce S).Subgraph, P.IsPerfectMatching :=
    perfect_matching_of_adjacency_involution _ f hi ha
  have hsize : S.ncard = 2*13 := by
    change (in1159_half_S : Set (Fin 52)).ncard = 2*13
    rw [Set.ncard_coe_finset]
    decide
  have hcomp : Sᶜ = {v : Fin 52 | v ∈ in1159_half_R} := by
    ext v
    simp [S,in1159_half_S]
  have hR := extendible_matchable_two_k_vertices_complement_matchable op1957_half_pool_example_graph 13 hext S hsize hS
  rw [hcomp] at hR
  have hU : in1159_half_U ⊆ in1159_half_R := by decide
  have hcover : ∀ u ∈ in1159_half_U, ∀ v ∈ in1159_half_R,
      op1957_half_pool_example_graph.Adj u v → v ∈ in1159_half_T := by decide
  have hb := induced_perfect_matching_neighbors_card_bound op1957_half_pool_example_graph in1159_half_R
    in1159_half_U in1159_half_T hU hcover hR
  have hn : ¬ in1159_half_U.card ≤ in1159_half_T.card := by decide
  exact hn hb
