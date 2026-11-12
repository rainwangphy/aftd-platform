import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op223_slide_leaf_pendant_chain_is_tree

Topic: graphs   Node: 133f8bb0c925

Provenance: helper lemma. step towards op223_gts_poset_connectivity

If v is a leaf of the tree X reached from u by a path p with all interior vertices of degree 2, and b is a neighbour of u outside p and not adjacent to v, then X − ub + vb is again a tree.
-/

/-- The single-edge leaf slide along a pendant chain preserves being a tree. -/
theorem op223_slide_leaf_pendant_chain_is_tree {V : Type*} [Fintype V] [DecidableEq V]
    (X : SimpleGraph V) (hX : X.IsTree) (u v b : V) (p : X.Walk u v)
    (huv : u ≠ v) (hp : p.IsPath)
    (hint : ∀ x ∈ p.support, x ≠ u → x ≠ v → Nat.card (X.neighborSet x) = 2)
    (hv : Nat.card (X.neighborSet v) = 1)
    (hub : X.Adj u b) (hvb : ¬ X.Adj v b) (hb : b ∉ p.support) :
    (X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}).IsTree := by
  let X' := X.deleteEdges {s(u, b)} ⊔ SimpleGraph.fromEdgeSet {s(v, b)}
  have hX_conn : X.Connected := (SimpleGraph.isTree_iff_connected_and_card.mp hX).1
  have hX_card : Nat.card ↑X.edgeSet + 1 = Nat.card V := (SimpleGraph.isTree_iff_connected_and_card.mp hX).2
  have : Nonempty V := hX_conn.nonempty
  have hvb_ne : v ≠ b := by
    rintro rfl
    exact hb p.end_mem_support
  have h_vb_adj : X'.Adj v b := by
    rw [SimpleGraph.sup_adj]
    right
    rw [SimpleGraph.fromEdgeSet_adj]
    exact ⟨rfl, hvb_ne⟩
  have h_p_edges : ∀ e ∈ p.edges, e ∈ X'.edgeSet := by
    intro e he
    have he_in_X : e ∈ X.edgeSet := p.edges_subset_edgeSet he
    have he_ne : e ≠ s(u, b) := by
      rintro rfl
      have : b ∈ p.support := p.mem_support_of_mem_edges he (Sym2.mem_mk_right u b)
      exact hb this
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges]
    left
    exact ⟨he_in_X, fun h => he_ne (Set.mem_singleton_iff.mp h)⟩
  have h_uv_reach : X'.Reachable u v := ⟨p.transfer X' h_p_edges⟩
  have h_ub_reach : X'.Reachable u b := h_uv_reach.trans h_vb_adj.reachable
  have h_reach : ∀ ⦃x y : V⦄, X.Adj x y → X'.Reachable x y := by
    intro x y hxy
    by_cases h : s(x, y) = s(u, b)
    · rw [Sym2.eq_iff] at h
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h_ub_reach
      · exact h_ub_reach.symm
    · have : X'.Adj x y := by
        rw [SimpleGraph.sup_adj]
        left
        rw [SimpleGraph.deleteEdges_adj]
        exact ⟨hxy, fun h' => h (Set.mem_singleton_iff.mp h')⟩
      exact this.reachable
  have h_preconn : X'.Preconnected := by
    intro x y
    obtain ⟨w⟩ := hX_conn.preconnected x y
    induction w with
    | nil => exact SimpleGraph.Reachable.refl _
    | cons hadj _ ih => exact (h_reach hadj).trans ih
  have h_conn : X'.Connected := ⟨h_preconn⟩
  have h_edgeSet : X'.edgeSet = (X.edgeSet \ {s(u, b)}) ∪ {s(v, b)} := by
    dsimp [X']
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_deleteEdges, SimpleGraph.edgeSet_fromEdgeSet]
    have : ({s(v, b)} : Set (Sym2 V)) \ Sym2.diagSet = {s(v, b)} := by
      rw [sdiff_eq_self_iff_disjoint]
      rw [Set.disjoint_singleton_right]
      rw [Sym2.mem_diagSet, Sym2.mk_isDiag_iff]
      exact hvb_ne
    rw [this]
  have ha : s(u, b) ∈ X.edgeSet := (SimpleGraph.mem_edgeSet X).mpr hub
  have h_not : s(v, b) ∉ X.edgeSet := mt (SimpleGraph.mem_edgeSet X).mp hvb
  have h_ncard : ((X.edgeSet \ {s(u, b)}) ∪ {s(v, b)}).ncard = X.edgeSet.ncard := by
    have : (X.edgeSet \ {s(u, b)}) ∪ {s(v, b)} = insert s(v, b) (X.edgeSet \ {s(u, b)}) := by
      exact Set.union_singleton
    rw [this]
    have hb' : s(v, b) ∉ X.edgeSet \ {s(u, b)} := fun h => h_not h.1
    rw [Set.ncard_insert_of_notMem hb']
    have := Set.ncard_sdiff_singleton_add_one ha
    omega
  have h_card : Nat.card ↑X'.edgeSet + 1 = Nat.card V := by
    rw [Nat.card_coe_set_eq, h_edgeSet, h_ncard, ← Nat.card_coe_set_eq]
    exact hX_card
  exact SimpleGraph.isTree_iff_connected_and_card.mpr ⟨h_conn, h_card⟩
