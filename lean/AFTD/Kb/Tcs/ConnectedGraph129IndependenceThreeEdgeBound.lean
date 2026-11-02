import AFTD.Prelude
import AFTD.Kb.Tcs.Order
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# connected_graph_129_independence_three_edge_bound

Topic: graphs   Node: 3a6e7b22c697

Provenance: helper lemma. Equality-case refinement of the common-in-neighbor graph count in arXiv:2610.11517 Proposition 4.3 and DOI:10.1006/jctb.1996.0062 Claim 2, serving OP-110.

Every connected simple graph on 129 vertices with no independent set of size four has at least 2710 edges.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem connected_graph_129_independence_three_edge_bound
    (G : SimpleGraph (Fin 129)) [DecidableRel G.Adj]
    (hconn : G.Connected) (hindep : G.IndepSetFree 4) :
    2710 ≤ G.edgeFinset.card := by
  classical
  by_contra hbad
  have hlow : G.edgeFinset.card ≤ 2709 := by omega
  let H := Gᶜ
  have hfree : H.CliqueFree 4 := by simpa [H] using hindep
  have hupper : H.edgeFinset.card ≤ 5547 := by
    have h := SimpleGraph.CliqueFree.card_edgeFinset_le (G := H) (r := 3) hfree
    norm_num at h
    exact h
  have hdis : Disjoint G.edgeFinset H.edgeFinset := by
    rw [SimpleGraph.disjoint_edgeFinset]
    change Disjoint G Gᶜ
    exact disjoint_compl_right
  have hunion : G.edgeFinset ∪ H.edgeFinset = (⊤ : SimpleGraph (Fin 129)).edgeFinset := by
    rw [← SimpleGraph.edgeFinset_sup]
    change (G ⊔ Gᶜ).edgeFinset = _
    exact SimpleGraph.edgeFinset_inj.mpr sup_compl_eq_top
  have hsum : G.edgeFinset.card + H.edgeFinset.card = 8256 := by
    rw [← Finset.card_union_of_disjoint hdis, hunion, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    rw [Nat.choose_two_right]
    norm_num
  have heq : H.edgeFinset.card = 5547 := by omega
  have hmax : H.IsTuranMaximal 3 := by
    refine ⟨hfree, ?_⟩
    intro F inst hF
    have hf := SimpleGraph.CliqueFree.card_edgeFinset_le (G := F) (r := 3) hF
    norm_num at hf
    omega
  have hiso : Nonempty (H ≃g SimpleGraph.turanGraph 129 3) := by
    have h := (SimpleGraph.isTuranMaximal_iff_nonempty_iso_turanGraph (G := H) (r := 3) (by decide)).mp hmax
    rw [Fintype.card_fin] at h
    exact h
  obtain ⟨e⟩ := hiso
  have hsame : ∀ u v : Fin 129, G.Adj u v → (e u).val % 3 = (e v).val % 3 := by
    intro u v huv
    have hn : ¬ H.Adj u v := by simp [H, SimpleGraph.compl_adj, huv]
    have ht : ¬ (SimpleGraph.turanGraph 129 3).Adj (e u) (e v) := by
      intro ht
      exact hn (e.map_adj_iff.mp ht)
    simpa [SimpleGraph.turanGraph_adj] using ht
  have hreach : ∀ u v : Fin 129, G.Reachable u v → (e u).val % 3 = (e v).val % 3 := by
    intro u v hr
    obtain ⟨p⟩ := hr
    induction p with
    | nil => rfl
    | cons h p ih => exact (hsame _ _ h).trans ih
  have hcontra := hreach (e.symm 0) (e.symm 1) (hconn _ _)
  simp only [e.apply_symm_apply] at hcontra
  norm_num at hcontra
