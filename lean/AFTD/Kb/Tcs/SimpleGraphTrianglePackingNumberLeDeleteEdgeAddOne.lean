import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumberEqZeroOfCliqueFree

/-!
# simple_graph_triangle_packing_number_le_delete_edge_add_one

Topic: graphs   Node: 02ca1fbc3a38

Provenance: helper lemma. step towards simple_graph_triangle_cover_number_le_two_mul_packing_number

Deleting an edge e from G decreases the triangle packing number by at most 1: ν(G) ≤ ν(G \ {e}) + 1.
-/

/-- Deleting an edge e from G decreases the triangle packing number by at most 1: ν(G) ≤ ν(G \ {e}) + 1. -/
theorem simple_graph_triangle_packing_number_le_delete_edge_add_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    simple_graph_triangle_packing_number G ≤ simple_graph_triangle_packing_number (G.deleteEdges {e}) + 1 := by
  classical
  set P : Set ℕ := {n | ∃ T : Finset (Finset V), (∀ t ∈ T, G.IsNClique 3 t) ∧
    (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} with hP
  have hbdd : BddAbove P := by
    refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
    rintro n ⟨T, -, -, rfl⟩
    exact Finset.card_le_univ T
  have hne : P.Nonempty := ⟨0, ∅, by simp, by simp, rfl⟩
  obtain ⟨T, hT, hTp, hTc⟩ := Nat.sSup_mem hne hbdd
  have hG_eq : simple_graph_triangle_packing_number G = T.card := by
    change sSup P = T.card
    exact hTc.symm
  let p : Finset V → Prop := fun t => ∀ x ∈ e, x ∈ t
  have hp_card : (T.filter p).card ≤ 1 := by
    obtain ⟨u, v, huv, rfl⟩ : ∃ u v, u ≠ v ∧ e = s(u, v) := by
      have hdiag := G.not_isDiag_of_mem_edgeSet he
      induction' e using Sym2.inductionOn with u v
      simp only [Sym2.mk_isDiag_iff] at hdiag
      exact ⟨u, v, hdiag, rfl⟩
    rw [Finset.card_le_one_iff]
    intro t1 t2 ht1 ht2
    rw [Finset.mem_filter] at ht1 ht2
    by_contra hne_t
    have hpw := hTp ht1.1 ht2.1 hne_t
    have hu1 : u ∈ t1 := ht1.2 u (by simp)
    have hv1 : v ∈ t1 := ht1.2 v (by simp)
    have hu2 : u ∈ t2 := ht2.2 u (by simp)
    have hv2 : v ∈ t2 := ht2.2 v (by simp)
    have h2 : 2 ≤ (t1 ∩ t2).card := by
      have h_sub : {u, v} ⊆ t1 ∩ t2 := by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · simp [hu1, hu2]
        · simp [hv1, hv2]
      have h_card : ({u, v} : Finset V).card = 2 := Finset.card_pair huv
      rw [← h_card]
      exact Finset.card_le_card h_sub
    omega
  let T' := T.filter (fun t => ¬ p t)
  have hT'_card : T.card ≤ T'.card + 1 := by
    have hsplit : (T.filter p).card + T'.card = T.card := Finset.card_filter_add_card_filter_not p
    omega
  have hT'_clique : ∀ t ∈ T', (G.deleteEdges {e}).IsNClique 3 t := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htT, hnot_p⟩ := ht
    have hclique := hT t htT
    refine ⟨?_, hclique.card_eq⟩
    intro x hx y hy hxy
    rw [SimpleGraph.deleteEdges_adj]
    refine ⟨hclique.isClique hx hy hxy, ?_⟩
    intro heq
    simp only [Set.mem_singleton_iff] at heq
    apply hnot_p
    intro z hz
    rw [← heq] at hz
    simp only [Sym2.mem_iff] at hz
    rcases hz with rfl | rfl
    · exact hx
    · exact hy
  have hT'_pw : (T' : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) := by
    refine hTp.mono ?_
    intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    exact Finset.mem_coe.2 ht.1
  have hT'_le : T'.card ≤ simple_graph_triangle_packing_number (G.deleteEdges {e}) := by
    unfold simple_graph_triangle_packing_number
    have hbdd' : BddAbove {n | ∃ T : Finset (Finset V),
        (∀ t ∈ T, (G.deleteEdges {e}).IsNClique 3 t) ∧
        (T : Set (Finset V)).Pairwise (fun s t => (s ∩ t).card ≤ 1) ∧ T.card = n} := by
      refine ⟨(Finset.univ : Finset (Finset V)).card, ?_⟩
      rintro n ⟨T'', -, -, rfl⟩
      exact Finset.card_le_univ T''
    exact le_csSup hbdd' ⟨T', hT'_clique, hT'_pw, rfl⟩
  omega
