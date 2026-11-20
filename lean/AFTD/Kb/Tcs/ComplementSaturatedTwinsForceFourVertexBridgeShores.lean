import AFTD.Prelude

/-!
# complement_saturated_twins_force_four_vertex_bridge_shores

Topic: graphs   Node: 22975f28d989

Provenance: helper lemma. Structural shore-size step for the OP-1957 saturated-twin equality branch, suggested by experiments 34916 and 34917.

Let H have maximum degree at most d, and let adjacent vertices x,y be complement twins with x of degree d. Let Q and W be even sets of at least two vertices, with x and y outside Q, W contained in the neighbors of x other than y, all Q-W pairs adjacent in H, and |Q|+|W|=d+1. Suppose two vertices u,v in that neighbor set have no common neighbor outside x,y. Then each of Q and W has at least four vertices.
-/

theorem complement_saturated_twins_force_four_vertex_bridge_shores
    {n d : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (x y u v : Fin n) (Q W : Finset (Fin n))
    (hxy : H.Adj x y) (hxdeg : (H.neighborFinset x).card = d)
    (hmax : ∀ a, (H.neighborFinset a).card ≤ d)
    (htwin : ∀ a, a ≠ x → a ≠ y → (H.Adj x a ↔ H.Adj y a))
    (hqx : x ∉ Q) (hqy : y ∉ Q)
    (hw : W ⊆ (H.neighborFinset x).erase y)
    (hu : u ∈ (H.neighborFinset x).erase y)
    (hv : v ∈ (H.neighborFinset x).erase y)
    (hcommon : ∀ a, H.Adj u a → H.Adj v a → a = x ∨ a = y)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, H.Adj q w)
    (hqmin : 2 ≤ Q.card) (hwmin : 2 ≤ W.card)
    (hqe : Even Q.card) (hwe : Even W.card)
    (hsum : Q.card + W.card = d + 1) :
    4 ≤ Q.card ∧ 4 ≤ W.card := by
  have h4W : 4 ≤ W.card := by
    have hWne : W.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨w, hwW⟩ := hWne
    have hwx : w ∈ (H.neighborFinset x).erase y := hw hwW
    have hwx_adj : H.Adj x w := by
      have := Finset.mem_of_mem_erase hwx
      rwa [SimpleGraph.mem_neighborFinset] at this
    have hwx_adj' : H.Adj w x := hwx_adj.symm
    have hwy_ne : w ≠ y := Finset.ne_of_mem_erase hwx
    have hwx_ne : w ≠ x := hwx_adj'.ne
    have hwy_adj : H.Adj y w := (htwin w hwx_ne hwy_ne).mp hwx_adj
    have hwy_adj' : H.Adj w y := hwy_adj.symm
    have hsub : insert x (insert y Q) ⊆ H.neighborFinset w := by
      intro z hz
      simp only [Finset.mem_insert] at hz
      rcases hz with rfl | rfl | hz
      · rwa [SimpleGraph.mem_neighborFinset]
      · rwa [SimpleGraph.mem_neighborFinset]
      · rw [SimpleGraph.mem_neighborFinset]
        exact (hcross z hz w hwW).symm
    have hcard_sub := Finset.card_le_card hsub
    have hx_ne_y : x ≠ y := hxy.ne
    have hx_not_in : x ∉ insert y Q := by
      intro h
      simp only [Finset.mem_insert] at h
      rcases h with rfl | h
      · exact hx_ne_y rfl
      · exact hqx h
    rw [Finset.card_insert_of_notMem hx_not_in, Finset.card_insert_of_notMem hqy] at hcard_sub
    have hw_deg : (H.neighborFinset w).card ≤ d := hmax w
    have hQd : Q.card + 2 ≤ d := by omega
    have : 3 ≤ W.card := by omega
    rcases hwe with ⟨m, hm⟩
    omega
  have h4Q : 4 ≤ Q.card := by
    by_contra! hlt
    have hq2 : Q.card = 2 := by
      rcases hqe with ⟨m, hm⟩
      omega
    have hy_mem : y ∈ H.neighborFinset x := by
      rwa [SimpleGraph.mem_neighborFinset]
    have herase_card : ((H.neighborFinset x).erase y).card = d - 1 := by
      rw [Finset.card_erase_of_mem hy_mem, hxdeg]
    have hW_card : W.card = d - 1 := by omega
    have hW_eq : W = (H.neighborFinset x).erase y := by
      apply Finset.eq_of_subset_of_card_le hw
      omega
    have huW : u ∈ W := by rwa [hW_eq]
    have hvW : v ∈ W := by rwa [hW_eq]
    have hQne : Q.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨q, hqQ⟩ := hQne
    have huq : H.Adj u q := (hcross q hqQ u huW).symm
    have hvq : H.Adj v q := (hcross q hqQ v hvW).symm
    have hqxy : q = x ∨ q = y := hcommon q huq hvq
    rcases hqxy with rfl | rfl
    · exact hqx hqQ
    · exact hqy hqQ
  exact ⟨h4Q, h4W⟩
