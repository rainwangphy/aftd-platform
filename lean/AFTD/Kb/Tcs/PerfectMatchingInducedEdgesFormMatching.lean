import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# perfect_matching_induced_edges_form_matching

Topic: graphs   Node: 6736d816b7b2

Provenance: helper lemma. Balanced-cut matching symmetry for OP-1957; https://arxiv.org/abs/2611.22690.

The edges of a perfect matching internal to a given vertex set form a matching supported on that set.
-/

theorem perfect_matching_induced_edges_form_matching
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching) (S : Finset V) :
    ∃ Q : G.Subgraph, Q.IsMatching ∧ Q.verts ⊆ (S : Set V) ∧
      Q ≤ P ∧ Q.edgeSet = (P.induce (S : Set V)).edgeSet := by
  set_option maxHeartbeats 4000000 in
    classical
    let f : V → V := fun v => (hP.1 (hP.2 v)).choose
    have hf : ∀ v, P.Adj v (f v) := by
      intro v
      exact (hP.1 (hP.2 v)).choose_spec.1
    have hinv : Function.Involutive f := by
      intro v
      exact (hP.1 (hP.2 (f v))).unique (hf (f v)) (hf v).symm
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
    have hsub : Q.verts ⊆ (S : Set V) := by intro v hv; exact hv.1
    have hle : Q ≤ P := by
      constructor
      · intro v hv
        exact hP.2 v
      · intro u v h
        exact h.1
    exact ⟨Q,hQ,hsub,hle,hedge⟩
