import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphCommonPredecessorGraph
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# digraph_common_predecessor_vertex_incidence_bound

Topic: graphs   Node: 94300136c597

Provenance: helper lemma. Exceptional-vertex incidence bound in the general minimum-counterexample campaign route to OP-110.

For an r-outregular finite digraph, the number of common-predecessor edge incidences repeated at a given vertex is at most the total number of repeated edge incidences.
-/

private instance in478_predecessor_incidence_decAdj {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] : DecidableRel (digraph_common_predecessor_graph D).Adj := by
  intro u v
  unfold digraph_common_predecessor_graph
  infer_instance

theorem digraph_common_predecessor_vertex_incidence_bound
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (r : ℕ) (hreg : ∀ v, (Finset.univ.filter fun w => D.Adj v w).card = r) (v : α) :
    (r - 1) * (Finset.univ.filter fun u => D.Adj u v).card +
      (digraph_common_predecessor_graph D).edgeFinset.card ≤
    (digraph_common_predecessor_graph D).degree v + Fintype.card α * Nat.choose r 2 := by
  let G := digraph_common_predecessor_graph D
  let edgesAt : α → Finset (Sym2 α) := fun w =>
    ((Finset.univ.filter (fun u => D.Adj w u)).offDiag).image (Function.uncurry Sym2.mk)
  have h_edge_split := Finset.card_filter_add_card_filter_not (s := G.edgeFinset) (v ∈ ·)
  have h_deg : (G.edgeFinset.filter (v ∈ ·)).card = G.degree v := by
    rw [← SimpleGraph.incidenceFinset_eq_filter, SimpleGraph.card_incidenceFinset_eq_degree]
  have h_edge_le : (G.edgeFinset.filter (v ∉ ·)).card ≤ ∑ w : α, ((edgesAt w).filter (v ∉ ·)).card := by
    have hsub : G.edgeFinset.filter (v ∉ ·) ⊆ (Finset.univ : Finset α).biUnion (fun w => (edgesAt w).filter (v ∉ ·)) := by
      intro e he
      rw [Finset.mem_filter] at he
      have he_edge := he.1
      have hve := he.2
      induction e using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] at he_edge
        dsimp [digraph_common_predecessor_graph, G] at he_edge
        rcases he_edge with ⟨hne, w, hwx, hwy⟩
        apply Finset.mem_biUnion.mpr
        refine ⟨w, Finset.mem_univ _, ?_⟩
        rw [Finset.mem_filter]
        refine ⟨?_, hve⟩
        simp only [edgesAt, Finset.mem_image, Finset.mem_offDiag,
          Function.uncurry_apply_pair, Prod.exists, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨x, y, ⟨hwx, hwy, hne⟩, rfl⟩
    calc
      (G.edgeFinset.filter (v ∉ ·)).card ≤
          ((Finset.univ : Finset α).biUnion (fun w => (edgesAt w).filter (v ∉ ·))).card :=
        Finset.card_le_card hsub
      _ ≤ ∑ w : α, ((edgesAt w).filter (v ∉ ·)).card := Finset.card_biUnion_le
  have h_filter_v : ∀ w, ((edgesAt w).filter (v ∈ ·)).card = if D.Adj w v then r - 1 else 0 := by
    intro w
    split_ifs with hwv
    · have h_img : (edgesAt w).filter (v ∈ ·) =
          (((Finset.univ.filter (fun u => D.Adj w u)).erase v).image (fun u => s(v, u))) := by
        ext e
        simp only [edgesAt, Finset.mem_filter, Finset.mem_image, Finset.mem_erase, Finset.mem_offDiag,
          Function.uncurry_apply_pair, Prod.exists]
        constructor
        · rintro ⟨⟨x, y, ⟨hx, hy, hne⟩, rfl⟩, hve⟩
          simp only [Sym2.mem_iff] at hve
          rcases hve with rfl | rfl
          · exact ⟨y, ⟨hne.symm, hy⟩, rfl⟩
          · exact ⟨x, ⟨hne, hx⟩, Sym2.eq_swap⟩
        · rintro ⟨u, ⟨hne, hu⟩, rfl⟩
          refine ⟨⟨v, u, ⟨?_, hu, hne.symm⟩, rfl⟩, by simp⟩
          simp [hwv]
      rw [h_img]
      rw [Finset.card_image_of_injOn]
      · have he : ((Finset.univ.filter (fun u => D.Adj w u)).erase v).card + 1 =
            (Finset.univ.filter (fun u => D.Adj w u)).card :=
          Finset.card_erase_add_one (by simp [hwv])
        have hd : (Finset.univ.filter (fun u => D.Adj w u)).card = r := hreg w
        omega
      · intro x hx y _ hxy
        have hxne : x ≠ v := (Finset.mem_erase.mp hx).1
        simp only [Sym2.eq_iff] at hxy
        rcases hxy with ⟨_, rfl⟩ | ⟨_, rfl⟩
        · rfl
        · exact (hxne rfl).elim
    · apply Finset.card_eq_zero.mpr
      rw [Finset.filter_eq_empty_iff]
      intro e he hve
      simp only [edgesAt, Finset.mem_image, Finset.mem_offDiag,
        Function.uncurry_apply_pair, Prod.exists] at he
      rcases he with ⟨x, y, ⟨hx, hy, _⟩, rfl⟩
      simp only [Sym2.mem_iff] at hve
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
      rcases hve with rfl | rfl
      · exact hwv hx
      · exact hwv hy
  have h_sum_filter_v : ∑ w : α, ((edgesAt w).filter (v ∈ ·)).card =
      (r - 1) * (Finset.univ.filter fun u => D.Adj u v).card := by
    calc
      ∑ w : α, ((edgesAt w).filter (v ∈ ·)).card =
          ∑ w : α, (if D.Adj w v then r - 1 else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        exact h_filter_v w
      _ = (r - 1) * (Finset.univ.filter fun u => D.Adj u v).card := by
        rw [Finset.sum_ite]
        simp [Nat.mul_comm]
  have h_edgesAt_card : ∀ w, (edgesAt w).card = Nat.choose r 2 := by
    intro w
    change (((Finset.univ.filter (fun u => D.Adj w u)).offDiag).image (Function.uncurry Sym2.mk)).card =
      Nat.choose r 2
    rw [Sym2.card_image_offDiag]
    rw [hreg w]
  have h_sum_both : ∑ w : α, ((edgesAt w).filter (v ∈ ·)).card +
      ∑ w : α, ((edgesAt w).filter (v ∉ ·)).card = Fintype.card α * Nat.choose r 2 := by
    rw [← Finset.sum_add_distrib]
    calc
      ∑ w : α, (((edgesAt w).filter (v ∈ ·)).card + ((edgesAt w).filter (v ∉ ·)).card) =
          ∑ w : α, (edgesAt w).card := by
        apply Finset.sum_congr rfl
        intro w _
        exact Finset.card_filter_add_card_filter_not (v ∈ ·)
      _ = ∑ _w : α, Nat.choose r 2 := by
        apply Finset.sum_congr rfl
        intro w _
        exact h_edgesAt_card w
      _ = Fintype.card α * Nat.choose r 2 := by
        simp
  linarith
