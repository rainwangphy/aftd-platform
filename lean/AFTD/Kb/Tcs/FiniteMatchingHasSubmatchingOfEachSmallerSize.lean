import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# finite_matching_has_submatching_of_each_smaller_size

Topic: graphs   Node: c57e5fd63a72

Provenance: helper lemma. OP-1957; restricting a finite matching to a specified number of its edges.

Every finite matching with at least k edges contains a submatching with exactly k edges.
-/

theorem finite_matching_has_submatching_of_each_smaller_size
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (M : G.Subgraph) (hM : M.IsMatching) (k : ℕ) (hk : k ≤ M.edgeSet.ncard) :
    ∃ N : G.Subgraph, N.IsMatching ∧ N ≤ M ∧ N.edgeSet.ncard = k := by
  set_option maxHeartbeats 4000000 in
    classical
    let F : Finset (Sym2 V) := M.edgeSet.toFinset
    have hF : k ≤ F.card := by
      dsimp [F]
      rw [← Set.ncard_eq_toFinset_card']
      exact hk
    obtain ⟨E,hEF,hEcard⟩ := Finset.exists_subset_card_eq hF
    have hEM : ∀ u v, s(u,v) ∈ E → M.Adj u v := by
      intro u v h
      have hh := hEF h
      change s(u,v) ∈ M.edgeSet.toFinset at hh
      exact SimpleGraph.Subgraph.mem_edgeSet.mp (Set.mem_toFinset.mp hh)
    let N : G.Subgraph := {
      verts := {v | ∃ w, s(v,w) ∈ E}
      Adj := fun u v => s(u,v) ∈ E
      adj_sub := by intro u v h; exact M.adj_sub (hEM u v h)
      edge_vert := by intro u v h; exact ⟨v,h⟩
      symm := ⟨by intro u v h; simpa [Sym2.eq_swap] using h⟩ }
    have hN : N.IsMatching := by
      intro v hv
      obtain ⟨w,hw⟩ := hv
      have hMv := hEM v w hw
      refine ⟨w,hw,?_⟩
      intro z hz
      exact (hM (M.edge_vert hMv)).unique (hEM v z hz) hMv
    have hNM : N ≤ M := by
      constructor
      · intro v hv
        obtain ⟨w,hw⟩ := hv
        exact M.edge_vert (hEM v w hw)
      · intro u v huv
        exact hEM u v huv
    have hcard : N.edgeSet.ncard = k := by
      have heq : N.edgeSet = (E : Set (Sym2 V)) := by
        ext e
        induction e using Sym2.inductionOn with
        | _ u v => rfl
      rw [heq,Set.ncard_coe_finset,hEcard]
    exact ⟨N,hN,hNM,hcard⟩
