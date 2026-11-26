import AFTD.Prelude
import AFTD.Kb.Tcs.Op1957HiddenBarrierGraph
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.PerfectMatchingOddAnticompleteGroupsBound
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution

/-!
# op1957_hidden_barrier_not_extendible

Topic: graphs   Node: 77066fbe052f

Provenance: helper lemma. OP-1957; hidden barrier relaxation, experiment 40492.

The 40-vertex hidden-barrier graph is not 10-extendible.
-/

theorem op1957_hidden_barrier_not_extendible : ¬ is_k_extendable op1957_hidden_barrier_graph 10 := by
  set_option maxHeartbeats 4000000 in
    classical
    intro hext
    let S := {v : Fin 40 | v ∈ in1209_hidden_S}
    let f (v : S) : S := ⟨in1209_hidden_mate v.val, by revert v; decide⟩
    have hi : Function.Involutive f := by intro v; revert v; decide
    have ha : ∀ v : S, (op1957_hidden_barrier_graph.induce S).Adj v (f v) := by
      intro v
      revert v
      decide
    have hS : ∃ P : (op1957_hidden_barrier_graph.induce S).Subgraph, P.IsPerfectMatching :=
      perfect_matching_of_adjacency_involution _ f hi ha
    have hsize : S.ncard = 2*10 := by
      change (in1209_hidden_S : Set (Fin 40)).ncard = 2*10
      rw [Set.ncard_coe_finset]
      decide
    have hcomp : Sᶜ = {v : Fin 40 | v ∈ in1209_hidden_R} := by
      ext v
      simp [S,in1209_hidden_R]
    have hR := extendible_matchable_two_k_vertices_complement_matchable op1957_hidden_barrier_graph 10 hext S hsize hS
    rw [hcomp] at hR
    let R : Set (Fin 40) := {v | v ∈ in1209_hidden_R}
    let J : Finset (Fin 7) := Finset.univ
    let F : Fin 7 → Finset R := fun i => Finset.univ.filter (fun v => v.val ∈ in1209_hidden_group i)
    let L : Finset R := Finset.univ.filter (fun v => v.val.val < 20)
    have hsub : ∀ i ∈ J, F i ⊆ L := by
      intro i hi
      revert i
      decide
    have hodd : ∀ i ∈ J, Odd (F i).card := by
      intro i hi
      revert i
      decide
    have hdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      revert i j
      decide
    have hanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ (op1957_hidden_barrier_graph.induce R).Adj u v := by
      intro i hi
      revert i
      decide
    obtain ⟨P,hP⟩ := hR
    have hb := perfect_matching_odd_anticomplete_groups_bound (op1957_hidden_barrier_graph.induce R) P hP J F L hsub hodd hdis hanti
    have hn : ¬ J.card ≤ ((Finset.univ : Finset R) \ L).card := by decide
    exact hn hb
