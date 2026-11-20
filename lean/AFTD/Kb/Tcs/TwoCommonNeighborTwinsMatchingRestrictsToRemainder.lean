import AFTD.Prelude

/-!
# two_common_neighbor_twins_matching_restricts_to_remainder

Topic: graphs   Node: 19f7160b62ff

Provenance: helper lemma. First equality-witness residual matching restriction in the OP-1957 two-bridge campaign.

Suppose a perfect matching contains uv, the vertices outside S are the four distinct vertices x,y,p,q, and x and y each have precisely p,q as their graph neighbors. If u,v lie in S, then S minus u,v induces a perfect matching.
-/

lemma two_common_neighbor_twins_matching_restricts_to_remainder_four_verts_matched
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (x y p q : V)
    (hdistinct : ([x, y, p, q] : List V).Nodup)
    (hx : ∀ z, G.Adj x z ↔ z = p ∨ z = q)
    (hy : ∀ z, G.Adj y z ↔ z = p ∨ z = q) :
    ∀ w ∈ ({x, y, p, q} : Finset V), ∀ z, P.Adj w z → z = x ∨ z = y ∨ z = p ∨ z = q := by
  have hxy : x ≠ y := by
    simp only [List.nodup_cons, List.mem_cons, not_or] at hdistinct
    exact hdistinct.1.1
  have hP_mat := hP.1
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hP
  obtain ⟨wx, hxwx, hx_uniq⟩ := hP x
  obtain ⟨wy, hywy, hy_uniq⟩ := hP y
  have hwx_adj : G.Adj x wx := P.adj_sub hxwx
  have hwy_adj : G.Adj y wy := P.adj_sub hywy
  rw [hx] at hwx_adj
  rw [hy] at hwy_adj
  have hwx_ne_wy : wx ≠ wy := by
    rintro rfl
    exact hxy (hP_mat.eq_of_adj_right hxwx hywy)
  intro w hw z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · have : z = wx := hx_uniq z hz
    rw [this]
    rcases hwx_adj with rfl | rfl <;> simp
  · have : z = wy := hy_uniq z hz
    rw [this]
    rcases hwy_adj with rfl | rfl <;> simp
  · rcases hwx_adj with rfl | rfl
    · have : z = x := hP_mat.eq_of_adj_left hz (P.symm.symm _ _ hxwx)
      simp [this]
    · rcases hwy_adj with rfl | rfl
      · have : z = y := hP_mat.eq_of_adj_left hz (P.symm.symm _ _ hywy)
        simp [this]
      · exact (hwx_ne_wy rfl).elim
  · rcases hwx_adj with rfl | rfl
    · rcases hwy_adj with rfl | rfl
      · exact (hwx_ne_wy rfl).elim
      · have : z = y := hP_mat.eq_of_adj_left hz (P.symm.symm _ _ hywy)
        simp [this]
    · have : z = x := hP_mat.eq_of_adj_left hz (P.symm.symm _ _ hxwx)
      simp [this]

theorem two_common_neighbor_twins_matching_restricts_to_remainder
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (P : G.Subgraph) (hP : P.IsPerfectMatching)
    (S : Finset V) (x y p q u v : V)
    (hdistinct : ([x, y, p, q] : List V).Nodup)
    (hdisj : Disjoint S ({x, y, p, q} : Finset V))
    (hcover : S ∪ {x, y, p, q} = Finset.univ)
    (hu : u ∈ S) (hv : v ∈ S) (huv : P.Adj u v)
    (hx : ∀ z, G.Adj x z ↔ z = p ∨ z = q)
    (hy : ∀ z, G.Adj y z ↔ z = p ∨ z = q) :
    ∃ M : (G.induce {a | a ∈ S ∧ a ≠ u ∧ a ≠ v}).Subgraph,
      M.IsPerfectMatching := by
  have h4 := two_common_neighbor_twins_matching_restricts_to_remainder_four_verts_matched
    G P hP x y p q hdistinct hx hy
  let R : Set V := {a | a ∈ S ∧ a ≠ u ∧ a ≠ v}
  let M : (G.induce R).Subgraph := {
    verts := Set.univ
    Adj a b := P.Adj a.1 b.1
    adj_sub := fun h => P.adj_sub h
    edge_vert := fun _ => Set.mem_univ _
    symm := ⟨fun _ _ h => P.symm.symm _ _ h⟩
  }
  use M
  have hP_mat := hP.1
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff] at hP ⊢
  rintro ⟨z, hz_mem, hz_u, hz_v⟩
  obtain ⟨w, hzw, hw_uniq⟩ := hP z
  have hw_S : w ∈ S := by
    by_contra hw_not_S
    have hw_univ : w ∈ S ∪ ({x, y, p, q} : Finset V) := by rw [hcover]; exact Finset.mem_univ w
    simp only [Finset.mem_union] at hw_univ
    have hw_in_4 : w ∈ ({x, y, p, q} : Finset V) := hw_univ.resolve_left hw_not_S
    have hz_in_4 := h4 w hw_in_4 z (P.symm.symm _ _ hzw)
    have hz_4_finset : z ∈ ({x, y, p, q} : Finset V) := by
      rcases hz_in_4 with rfl | rfl | rfl | rfl <;> simp
    exact Finset.disjoint_right.mp hdisj hz_4_finset hz_mem
  have hw_u : w ≠ u := by
    rintro rfl
    have : z = v := hP_mat.eq_of_adj_left (P.symm.symm _ _ hzw) huv
    exact hz_v this
  have hw_v : w ≠ v := by
    rintro rfl
    have : z = u := hP_mat.eq_of_adj_left (P.symm.symm _ _ hzw) (P.symm.symm _ _ huv)
    exact hz_u this
  have hw_R : w ∈ R := ⟨hw_S, hw_u, hw_v⟩
  use ⟨w, hw_R⟩
  refine ⟨hzw, ?_⟩
  rintro ⟨w', hw'_R⟩ hw'_adj
  exact Subtype.ext (hw_uniq w' hw'_adj)
