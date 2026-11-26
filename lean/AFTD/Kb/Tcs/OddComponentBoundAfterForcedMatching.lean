import AFTD.Prelude
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# odd_component_bound_after_forced_matching

Topic: graphs   Node: 2a2a1bcc9c5b

Provenance: helper lemma. Odd-component transfer for OP-1957; https://arxiv.org/abs/2611.22690.

If a forced matching meets the far side only inside one selected odd component and leaves r vertices on the cut, the far side has at most r+1 odd components.
-/

theorem odd_component_bound_after_forced_matching
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (C : Finset (Fin (4*k)))
    (K : (G.induce {v | v ∉ C}).ConnectedComponent)
    (hK : K ∈ (G.induce {v | v ∉ C}).oddComponents)
    (P T : G.Subgraph) (hP : P.IsPerfectMatching) (hT : T.IsMatching) (hTP : T ≤ P)
    (hsub : T.verts ⊆ (C : Set (Fin (4*k))) ∪
      (in1206_component_vertices G {v | v ∉ C} K : Set (Fin (4*k))))
    (hremain : ((C : Set (Fin (4*k))) \ T.verts).ncard = r) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r+1 := by
  classical
  let R : Set (Fin (4*k)) := {v | v ∉ C}
  let H := G.induce R
  let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
  let J : Finset H.ConnectedComponent := O.erase K
  let F : H.ConnectedComponent → Finset (Fin (4*k)) := in1206_component_vertices G R
  let L : Finset (Fin (4*k)) := R.toFinset
  have hKO : K ∈ O := by simpa [O,R,H] using hK
  have hJcard : J.card + 1 = H.oddComponents.ncard := by
    have hh := Finset.card_erase_add_one hKO
    have hOcard : O.card = H.oddComponents.ncard := by
      dsimp [O]
      exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
    dsimp [J]
    rw [← hOcard]
    exact hh
  have hJne : ∀ i ∈ J, i ≠ K := by
    intro i hi
    exact (Finset.mem_erase.mp hi).1
  have hJodd : ∀ i ∈ J, Odd (F i).card := by
    intro i hi
    have hiO : i ∈ O := (Finset.mem_erase.mp hi).2
    have hiOdd : i ∈ H.oddComponents := by simpa [O] using hiO
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
    rcases hsub huT with huC | huK
    · exact huR huC
    · have hdis : Disjoint (F i) (F K) :=
        (induced_component_ambient_vertex_properties G R i K).2.2.1 (hJne i hi)
      exact Finset.disjoint_left.mp hdis hu huK
  have hbudget := odd_groups_budget_after_forced_matching G P T hP hT hTP J F L
    hJsub hJodd hJdis hJanti hJfree
  have hcount : ((Finset.univ \ L).filter (fun v => v ∉ T.verts)).card = r := by
    have heq : (((Finset.univ \ L).filter (fun v => v ∉ T.verts)) : Set (Fin (4*k))) =
        (C : Set (Fin (4*k))) \ T.verts := by
      ext v
      simp [L,R]
    rw [← Set.ncard_coe_finset,heq,hremain]
  rw [hcount] at hbudget
  change H.oddComponents.ncard ≤ r+1
  omega
