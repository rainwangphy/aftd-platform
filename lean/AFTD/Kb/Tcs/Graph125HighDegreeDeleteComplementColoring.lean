import AFTD.Prelude
import AFTD.Kb.Tcs.Order

/-!
# graph_125_high_degree_delete_complement_coloring

Topic: graphs   Node: 648138eebbe3

Provenance: helper lemma. Exceptional-vertex coloring transfer for OP-110, using https://arxiv.org/abs/1409.8665, Theorem 1.1.

If a graph on 125 vertices has independence number at most three and at most 2583 edges, deleting a vertex of degree at least 46 leaves a graph whose vertices can be partitioned into three cliques, assuming the displayed near-extremal coloring criterion on 124 vertices.
-/

set_option maxHeartbeats 2500000
set_option maxRecDepth 4096

theorem graph_125_high_degree_delete_complement_coloring
    (G : SimpleGraph (Fin 125)) [DecidableRel G.Adj] (x : Fin 125)
    (hindep : G.IndepSetFree 4) (hedges : G.edgeFinset.card ≤ 2583)
    (hdegree : 46 ≤ G.degree x)
    (hnear : ∀ (α : Type) [Fintype α] [DecidableEq α] (H : SimpleGraph α)
      [DecidableRel H.Adj], Fintype.card α = 124 → H.CliqueFree 4 →
      5086 ≤ H.edgeFinset.card → H.Colorable 3) :
    ∃ col : Fin 125 → Fin 3,
      ∀ u v, u ≠ x → v ≠ x → col u = col v → u ≠ v → G.Adj u v := by
  classical
  let H := Gᶜ
  let S : Set (Fin 125) := {x}ᶜ
  let H' := H.induce S
  have hfree : H.CliqueFree 4 := by simpa [H] using hindep
  have hfree' : H'.CliqueFree 4 := by
    rw [SimpleGraph.cliqueFree_induce_iff]
    intro t ht hc
    exact hfree t hc
  have hdis : Disjoint G.edgeFinset H.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    change Disjoint G Gᶜ
    exact disjoint_compl_right
  have hunion : G.edgeFinset ∪ H.edgeFinset = (⊤ : SimpleGraph (Fin 125)).edgeFinset := by
    rw [← SimpleGraph.edgeFinset_sup]
    change (G ⊔ Gᶜ).edgeFinset = _
    exact SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  have htotal : G.edgeFinset.card + H.edgeFinset.card = 7750 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rw [Nat.choose_two_right]
    norm_num
  have hH : 5167 ≤ H.edgeFinset.card := by omega
  have hdegH : H.degree x ≤ 78 := by
    have h := G.degree_compl (v := x)
    change H.degree x = Fintype.card (Fin 125) - 1 - G.degree x at h
    simp only [Fintype.card_fin] at h
    omega
  have hcard : Fintype.card S = 124 := by
    dsimp [S]
    rw [Fintype.card_compl_set]
    simp
  have hcount : H'.edgeFinset.card = H.edgeFinset.card - H.degree x := by
    dsimp [H',S]
    rw [SimpleGraph.card_edgeFinset_induce_compl_singleton, SimpleGraph.card_edgeFinset_deleteIncidenceSet]
  have hc : H'.Colorable 3 := hnear S H' hcard hfree' (by omega)
  obtain ⟨C⟩ := hc
  let col : Fin 125 → Fin 3 := fun v => if h : v ≠ x then C ⟨v, by simpa only [S, Set.mem_compl_iff, Set.mem_singleton_iff] using h⟩ else 0
  refine ⟨col, ?_⟩
  intro u v hu hv heq hne
  by_contra hn
  let u' : S := ⟨u, by simpa only [S, Set.mem_compl_iff, Set.mem_singleton_iff] using hu⟩
  let v' : S := ⟨v, by simpa only [S, Set.mem_compl_iff, Set.mem_singleton_iff] using hv⟩
  have hh : H'.Adj u' v' := by
    change H.Adj u v
    simp [H, SimpleGraph.compl_adj, hne, hn]
  have hcolors := C.map_rel hh
  apply hcolors
  simpa only [col, dif_pos hu, dif_pos hv] using heq
