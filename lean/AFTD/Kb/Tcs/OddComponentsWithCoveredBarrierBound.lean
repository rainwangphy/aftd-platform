import AFTD.Prelude
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# odd_components_with_covered_barrier_bound

Topic: graphs   Node: 07c325096cc6

Provenance: helper lemma. Exposed-barrier reduction for OP-1957; https://arxiv.org/abs/2611.22690.

If a perfect matching extends a partial matching supported on C and X and covering X, then the odd components outside C and X are at most the remaining uncovered C vertices.
-/

theorem odd_components_with_covered_barrier_bound
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (C X : Finset (Fin (4*k)))
    (P T : G.Subgraph) (hP : P.IsPerfectMatching) (hT : T.IsMatching) (hTP : T ≤ P)
    (hTX : (X : Set (Fin (4*k))) ⊆ T.verts)
    (hTsub : T.verts ⊆ ((C ∪ X : Finset (Fin (4*k))) : Set (Fin (4*k))))
    (hremain : ((C : Set (Fin (4*k))) \ T.verts).ncard = r) :
    (G.induce {v | v ∉ C ∧ v ∉ X}).oddComponents.ncard ≤ r := by
  set_option maxHeartbeats 4000000 in
    classical
    let R : Set (Fin (4*k)) := {v | v ∉ C ∧ v ∉ X}
    let H := G.induce R
    let J : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let F : H.ConnectedComponent → Finset (Fin (4*k)) := in1206_component_vertices G R
    let L : Finset (Fin (4*k)) := R.toFinset
    have hJcard : J.card = H.oddComponents.ncard := by
      dsimp [J]
      exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
    have hJodd : ∀ i ∈ J, Odd (F i).card := by
      intro i hi
      have hiOdd : i ∈ H.oddComponents := by simpa [J] using hi
      have hc := (induced_component_ambient_vertex_properties G R i i).2.1
      rw [hc]
      exact hiOdd
    have hJsub : ∀ i ∈ J, F i ⊆ L := by
      intro i hi v hv
      have hh := (induced_component_ambient_vertex_properties G R i i).1 hv
      simpa [L] using hh
    have hJdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact (induced_component_ambient_vertex_properties G R i j).2.2.1 hij
    have hJanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ G.Adj u v := by
      intro i hi u hu v hv hvnot
      have hvR : v ∈ R := by simpa [L] using hv
      exact (induced_component_ambient_vertex_properties G R i i).2.2.2 u hu v hvR hvnot
    have hJfree : ∀ i ∈ J, ∀ u ∈ F i, u ∉ T.verts := by
      intro i hi u hu huT
      have huR : u ∈ R := (induced_component_ambient_vertex_properties G R i i).1 hu
      have huCX := hTsub huT
      rcases Finset.mem_union.mp huCX with huC | huX
      · exact huR.1 huC
      · exact huR.2 huX
    have hbudget := odd_groups_budget_after_forced_matching G P T hP hT hTP J F L
      hJsub hJodd hJdis hJanti hJfree
    have hcount : ((Finset.univ \ L).filter (fun v => v ∉ T.verts)).card = r := by
      have heq : (((Finset.univ \ L).filter (fun v => v ∉ T.verts)) : Set (Fin (4*k))) =
          (C : Set (Fin (4*k))) \ T.verts := by
        ext v
        by_cases ht : v ∈ T.verts
        · simp [ht]
        · have hnX : v ∉ X := fun hx => ht (hTX hx)
          simp [L,R,ht,hnX]
      rw [← Set.ncard_coe_finset,heq,hremain]
    rw [hcount,hJcard] at hbudget
    exact hbudget
