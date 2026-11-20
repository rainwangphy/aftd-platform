import AFTD.Prelude

/-!
# disjoint_matchable_shores_have_matching_avoiding_cross_edge

Topic: graphs   Node: 243d6155e882

Provenance: helper lemma. Full-union disjoint-shore exclusion in the OP-1957 two-bridge campaign.

If two disjoint vertex sets induce perfect matchings, then their union has a perfect matching avoiding every specified edge with one endpoint in each set.
-/

theorem disjoint_matchable_shores_have_matching_avoiding_cross_edge
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hdisj : Disjoint A B) (u v : V) (hu : u ∈ A) (hv : v ∈ B)
    (hA : ∃ M : (G.induce {z | z ∈ A}).Subgraph, M.IsPerfectMatching)
    (hB : ∃ M : (G.induce {z | z ∈ B}).Subgraph, M.IsPerfectMatching) :
    ∃ M : (G.induce {z | z ∈ A ∪ B}).Subgraph,
      M.IsPerfectMatching ∧
      ¬ M.Adj ⟨u, Finset.mem_union.mpr (Or.inl hu)⟩ ⟨v, Finset.mem_union.mpr (Or.inr hv)⟩ := by
  rcases hA with ⟨MA, hMA_mat, hMA_sp⟩
  rcases hB with ⟨MB, hMB_mat, hMB_sp⟩
  let M : (G.induce {z | z ∈ A ∪ B}).Subgraph := {
    verts := Set.univ
    Adj := fun x y => (∃ (hx : x.1 ∈ A) (hy : y.1 ∈ A), MA.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩) ∨
                      (∃ (hx : x.1 ∈ B) (hy : y.1 ∈ B), MB.Adj ⟨x.1, hx⟩ ⟨y.1, hy⟩)
    adj_sub := by
      rintro x y (⟨hx, hy, h⟩ | ⟨hx, hy, h⟩)
      · exact MA.adj_sub h
      · exact MB.adj_sub h
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨by
      rintro x y (⟨hx, hy, h⟩ | ⟨hx, hy, h⟩)
      · exact Or.inl ⟨hy, hx, MA.adj_symm h⟩
      · exact Or.inr ⟨hy, hx, MB.adj_symm h⟩⟩
  }
  use M
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro x _
    rcases Finset.mem_union.mp x.2 with hxA | hxB
    · have hx_sp : (⟨x.1, hxA⟩ : ↑{z | z ∈ A}) ∈ MA.verts := hMA_sp ⟨x.1, hxA⟩
      rcases hMA_mat hx_sp with ⟨wA, hwA_adj, hwA_uniq⟩
      have hw_mem : wA.1 ∈ A ∪ B := Finset.mem_union_left B wA.2
      let w : ↑{z | z ∈ A ∪ B} := ⟨wA.1, hw_mem⟩
      use w
      dsimp [ExistsUnique]
      refine ⟨?_, ?_⟩
      · left
        refine ⟨hxA, wA.2, ?_⟩
        have : (⟨w.1, wA.2⟩ : ↑{z | z ∈ A}) = wA := Subtype.ext rfl
        rw [this]
        exact hwA_adj
      · intro y hy
        rcases hy with ⟨hx', hy', hadj⟩ | ⟨hx', hy', hadj⟩
        · have h_eq : (⟨x.1, hx'⟩ : ↑{z | z ∈ A}) = ⟨x.1, hxA⟩ := Subtype.ext rfl
          rw [h_eq] at hadj
          have hy_eq := hwA_uniq ⟨y.1, hy'⟩ hadj
          apply Subtype.ext
          change y.1 = w.1
          have : (⟨y.1, hy'⟩ : ↑{z | z ∈ A}).1 = wA.1 := congrArg Subtype.val hy_eq
          exact this
        · have := Finset.disjoint_left.mp hdisj hxA
          exact False.elim (this hx')
    · have hx_sp : (⟨x.1, hxB⟩ : ↑{z | z ∈ B}) ∈ MB.verts := hMB_sp ⟨x.1, hxB⟩
      rcases hMB_mat hx_sp with ⟨wB, hwB_adj, hwB_uniq⟩
      have hw_mem : wB.1 ∈ A ∪ B := Finset.mem_union_right A wB.2
      let w : ↑{z | z ∈ A ∪ B} := ⟨wB.1, hw_mem⟩
      use w
      dsimp [ExistsUnique]
      refine ⟨?_, ?_⟩
      · right
        refine ⟨hxB, wB.2, ?_⟩
        have : (⟨w.1, wB.2⟩ : ↑{z | z ∈ B}) = wB := Subtype.ext rfl
        rw [this]
        exact hwB_adj
      · intro y hy
        rcases hy with ⟨hx', hy', hadj⟩ | ⟨hx', hy', hadj⟩
        · have := Finset.disjoint_right.mp hdisj hxB
          exact False.elim (this hx')
        · have h_eq : (⟨x.1, hx'⟩ : ↑{z | z ∈ B}) = ⟨x.1, hxB⟩ := Subtype.ext rfl
          rw [h_eq] at hadj
          have hy_eq := hwB_uniq ⟨y.1, hy'⟩ hadj
          apply Subtype.ext
          change y.1 = w.1
          have : (⟨y.1, hy'⟩ : ↑{z | z ∈ B}).1 = wB.1 := congrArg Subtype.val hy_eq
          exact this
  · intro x
    exact Set.mem_univ x
  · rintro (⟨hu', hv', hadj⟩ | ⟨hu', hv', hadj⟩)
    · have := Finset.disjoint_left.mp hdisj hv'
      exact this hv
    · have := Finset.disjoint_right.mp hdisj hu'
      exact this hu
