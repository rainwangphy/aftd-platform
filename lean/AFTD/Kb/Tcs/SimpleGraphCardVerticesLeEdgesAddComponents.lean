import AFTD.Prelude

/-!
# simple_graph_card_vertices_le_edges_add_components

Topic: graphs   Node: aa4272fce69a

Provenance: helper lemma. Structural necessity and certificate-soundness helpers for the OP-306 campaign; arXiv:2610.22142, Sections 3.3.1 and 3.3.2. These make the optimal block-partition route an equivalence at every odd order; no new exact wild-number case or bound is asserted.

In any finite simple graph, the number of vertices is at most the number of edges plus the number of connected components.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem simple_graph_card_vertices_le_edges_add_components {V : Type*} [Fintype V]
    (G : SimpleGraph V) :
    Fintype.card V ≤ G.edgeFinset.card + Fintype.card G.ConnectedComponent := by
  classical
  let A (C : G.ConnectedComponent) : Finset V := C.supp.toFinset
  let E (C : G.ConnectedComponent) : Finset (Sym2 V) := G.edgeFinset.filter (fun e => e.toFinset ⊆ A C)
  have hsumV : (∑ C : G.ConnectedComponent, (A C).card) = Fintype.card V := by
    have hi := Finset.card_eq_sum_card_fiberwise (f := G.connectedComponentMk)
      (s := (Finset.univ : Finset V)) (t := (Finset.univ : Finset G.ConnectedComponent))
      (fun _ _ => Finset.mem_univ _)
    have hA : ∀ C : G.ConnectedComponent, A C = Finset.univ.filter (fun v => G.connectedComponentMk v = C) := by
      intro C
      ext v
      simp only [A,Set.mem_toFinset,SimpleGraph.ConnectedComponent.mem_supp_iff,Finset.mem_filter,Finset.mem_univ,true_and]
    simp_rw [hA]
    simpa only [Finset.card_univ] using hi.symm
  have hc : ∀ C : G.ConnectedComponent, (A C).card ≤ (E C).card + 1 := by
    intro C
    have hset : (↑(A C) : Set V) = C.supp := by
      ext v
      simp only [A,Finset.mem_coe,Set.mem_toFinset]
    have hconn : (G.induce (↑(A C) : Set V)).Connected := by
      rw [hset]
      exact C.connected_toSimpleGraph
    have hi := hconn.card_vert_le_card_edgeSet_add_one
    have hv : Nat.card (↑(A C) : Set V) = (A C).card := by simp
    have he : Nat.card (G.induce (↑(A C) : Set V)).edgeSet = (E C).card := by
      rw [Nat.card_eq_fintype_card, ← SimpleGraph.edgeFinset_card]
      exact (G.card_filter_edgeFinset_toFinset_subset (A C)).symm
    rw [hv,he] at hi
    exact hi
  have hsumE : (∑ C : G.ConnectedComponent, (E C).card) ≤ G.edgeFinset.card := by
    simp_rw [E,Finset.card_eq_sum_ones,Finset.sum_filter]
    rw [Finset.sum_comm]
    calc _ ≤ ∑ _e ∈ G.edgeFinset, 1 := by
          apply Finset.sum_le_sum
          intro e he
          rw [← Finset.sum_filter, ← Finset.card_eq_sum_ones]
          rw [Finset.card_le_one]
          intro C hC D hD
          have hc := (Finset.mem_filter.1 hC).2
          have hd := (Finset.mem_filter.1 hD).2
          have hv : e.out.1 ∈ e.toFinset := Sym2.mem_toFinset.2 (Sym2.out_fst_mem e)
          have hCv : G.connectedComponentMk e.out.1 = C := by
            have hi : e.out.1 ∈ C.supp := by simpa only [A,Set.mem_toFinset] using hc hv
            exact hi
          have hDv : G.connectedComponentMk e.out.1 = D := by
            have hi : e.out.1 ∈ D.supp := by simpa only [A,Set.mem_toFinset] using hd hv
            exact hi
          exact hCv.symm.trans hDv
      _ = _ := by simp
  have hi := Finset.sum_le_sum (fun C (_ : C ∈ (Finset.univ : Finset G.ConnectedComponent)) => hc C)
  rw [hsumV,Finset.sum_add_distrib] at hi
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hi
  have hi' : Fintype.card V ≤ (∑ C : G.ConnectedComponent, (E C).card) + Fintype.card G.ConnectedComponent := by exact_mod_cast hi
  omega
