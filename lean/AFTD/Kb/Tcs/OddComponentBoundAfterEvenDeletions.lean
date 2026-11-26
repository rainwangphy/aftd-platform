import AFTD.Prelude
import AFTD.Kb.Tcs.OddGroupsBudgetAfterForcedMatching
import AFTD.Kb.Tcs.InducedComponentAmbientVertexProperties

/-!
# odd_component_bound_after_even_deletions

Topic: graphs   Node: 5e6bf1e62805

Provenance: helper lemma. Parity bookkeeping for OP-1957 balanced cuts; https://arxiv.org/abs/2611.22690.

A perfect matching extending a forced matching leaves at most r+1 odd components on the opposite side if the forced matching meets all but at most one odd component in an even number of vertices and leaves r vertices on the first side.
-/

theorem odd_component_bound_after_even_deletions
    (k r : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (C : Finset (Fin (4*k)))
    (P T : G.Subgraph) [DecidablePred (fun v => v ∈ T.verts)]
    (hP : P.IsPerfectMatching) (hT : T.IsMatching) (hTP : T ≤ P)
    (B : Finset (G.induce {v | v ∉ C}).ConnectedComponent) (hB : B.card ≤ 1)
    (hpar : ∀ i ∈ (G.induce {v | v ∉ C}).oddComponents.toFinset, i ∉ B →
      Even ((in1206_component_vertices G {v | v ∉ C} i) ∩ T.verts.toFinset).card)
    (hremain : ((C : Set (Fin (4*k))) \ T.verts).ncard = r) :
    (G.induce {v | v ∉ C}).oddComponents.ncard ≤ r+1 := by
  set_option maxHeartbeats 4000000 in
    classical
    let R : Set (Fin (4*k)) := {v | v ∉ C}
    let H := G.induce R
    let O : Finset H.ConnectedComponent := H.oddComponents.toFinset
    let J : Finset H.ConnectedComponent := O \ B
    let F : H.ConnectedComponent → Finset (Fin (4*k)) :=
      fun i => in1206_component_vertices G R i \ T.verts.toFinset
    let L : Finset (Fin (4*k)) := R.toFinset \ T.verts.toFinset
    have hJcard : H.oddComponents.ncard ≤ J.card + 1 := by
      have hO : O.card = H.oddComponents.ncard := by
        dsimp [O]
        exact (Set.ncard_eq_toFinset_card' H.oddComponents).symm
      have hcount := Finset.card_sdiff_add_card_inter O B
      have hinter : (O ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      dsimp [J]
      omega
    have hJodd : ∀ i ∈ J, Odd (F i).card := by
      intro i hi
      have hiO : i ∈ O := (Finset.mem_sdiff.mp hi).1
      have hiB : i ∉ B := (Finset.mem_sdiff.mp hi).2
      have hiOdd : i ∈ H.oddComponents := by simpa [O] using hiO
      have hc := (induced_component_ambient_vertex_properties G R i i).2.1
      have horig : Odd (in1206_component_vertices G R i).card := by
        rw [hc]
        exact hiOdd
      have heven := hpar i hiO hiB
      change Even ((in1206_component_vertices G R i) ∩ T.verts.toFinset).card at heven
      have hcount := Finset.card_sdiff_add_card_inter
        (in1206_component_vertices G R i) T.verts.toFinset
      rw [Nat.odd_iff] at horig ⊢
      rw [Nat.even_iff] at heven
      dsimp [F]
      omega
    have hJsub : ∀ i ∈ J, F i ⊆ L := by
      intro i hi v hv
      have hv' := Finset.mem_sdiff.mp hv
      have hh := (induced_component_ambient_vertex_properties G R i i).1 hv'.1
      apply Finset.mem_sdiff.mpr
      exact ⟨by simpa using hh, hv'.2⟩
    have hJdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (F i) (F j) := by
      intro i hi j hj hij
      exact ((induced_component_ambient_vertex_properties G R i j).2.2.1 hij).mono
        Finset.sdiff_subset Finset.sdiff_subset
    have hJanti : ∀ i ∈ J, ∀ u ∈ F i, ∀ v ∈ L, v ∉ F i → ¬ G.Adj u v := by
      intro i hi u hu v hv hvnot
      have hu' := Finset.mem_sdiff.mp hu
      have hv' := Finset.mem_sdiff.mp hv
      have hvR : v ∈ R := by simpa using hv'.1
      have hvcomp : v ∉ in1206_component_vertices G R i := by
        intro hh
        exact hvnot (Finset.mem_sdiff.mpr ⟨hh,hv'.2⟩)
      exact (induced_component_ambient_vertex_properties G R i i).2.2.2 u hu'.1 v hvR hvcomp
    have hJfree : ∀ i ∈ J, ∀ u ∈ F i, u ∉ T.verts := by
      intro i hi u hu
      simpa using (Finset.mem_sdiff.mp hu).2
    have hbudget := odd_groups_budget_after_forced_matching G P T hP hT hTP J F L
      hJsub hJodd hJdis hJanti hJfree
    have hcount : ((Finset.univ \ L).filter (fun v => v ∉ T.verts)).card = r := by
      have heq : (((Finset.univ \ L).filter (fun v => v ∉ T.verts)) : Set (Fin (4*k))) =
          (C : Set (Fin (4*k))) \ T.verts := by
        ext v
        by_cases ht : v ∈ T.verts
        · simp [ht]
        · simp [L,R,ht]
      rw [← Set.ncard_coe_finset,heq,hremain]
    rw [hcount] at hbudget
    change H.oddComponents.ncard ≤ r+1
    omega
