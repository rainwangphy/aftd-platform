import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleMatchableTwoKVerticesComplementMatchable

/-!
# perfect_matching_internal_edge_card

Topic: graphs   Node: db18141cd165

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

For a perfect matching and a specified matching-partner map, twice the number of internal edges is the number of vertices whose partners are internal.
-/

theorem perfect_matching_internal_edge_card
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (f : V → V)
    (hf : ∀ v, P.Adj v (f v)) (S : Finset V) :
    2*(P.induce (S : Set V)).edgeSet.ncard = (S.filter (fun v => f v ∈ S)).card := by
  set_option maxHeartbeats 4000000 in
    classical
    have hinv : Function.Involutive f := by
      intro v
      exact ((hP.1 (hP.2 (f v))).unique (hf (f v)) (hf v).symm)
    let Q : G.Subgraph := {
      verts := {v | v ∈ S ∧ f v ∈ S}
      Adj := fun u v => P.Adj u v ∧ u ∈ S ∧ v ∈ S
      adj_sub := by intro u v h; exact P.adj_sub h.1
      edge_vert := by
        intro u v h
        have hfv : f u = v := (hP.1 (hP.2 u)).unique (hf u) h.1
        exact ⟨h.2.1,hfv ▸ h.2.2⟩
      symm := ⟨by intro u v h; exact ⟨h.1.symm,h.2.2,h.2.1⟩⟩ }
    have hQ : Q.IsMatching := by
      intro v hv
      refine ⟨f v,⟨hf v,hv.1,hv.2⟩,?_⟩
      intro w hw
      exact (hP.1 (hP.2 v)).unique hw.1 (hf v)
    have hedge : Q.edgeSet = (P.induce (S : Set V)).edgeSet := by
      ext e
      induction e using Sym2.inductionOn with
      | _ u v =>
        simp [Q,SimpleGraph.Subgraph.mem_edgeSet,SimpleGraph.Subgraph.induce_adj,
          and_comm,and_left_comm,and_assoc]
    have hverts : Q.verts.ncard = (S.filter (fun v => f v ∈ S)).card := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext v
      simp [Q]
    have hh := in1076_matching_twice_card hQ
    rw [hedge,hverts] at hh
    exact hh
