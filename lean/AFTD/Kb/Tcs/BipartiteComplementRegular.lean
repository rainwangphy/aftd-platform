import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeTokenK2nDominationNumberFourGe

/-!
# bipartite_complement_regular

Topic: graphs   Node: 55162127acab

Provenance: helper lemma. arXiv:2611.00591 Lemma 4.1

Let H be an s-regular bipartite simple graph on parts V and W of size m. Then its bipartite complement K_{V,W} \ H is (m - s)-regular.
-/

open scoped Classical in
/-- The bipartite complement of an s-regular bipartite simple graph with parts of size m is (m - s)-regular. -/
theorem bipartite_complement_regular
    {V W : Type*} [Fintype V] [Fintype W]
    (m s : ℕ) (hV : Fintype.card V = m) (hW : Fintype.card W = m)
    (H : SimpleGraph (V ⊕ W)) (hH_sub : H ≤ completeBipartiteGraph V W)
    (hH_reg : H.IsRegularOfDegree s) :
    (completeBipartiteGraph V W \ H).IsRegularOfDegree (m - s) := by
  classical
  intro v
  change ((completeBipartiteGraph V W \ H).neighborFinset v).card = m - s
  rw [SimpleGraph.neighborFinset_sdiff]
  rw [Finset.card_sdiff_of_subset]
  · have hH_card : (H.neighborFinset v).card = s := by
      have : H.degree v = s := hH_reg v
      exact this
    rw [hH_card]
    rcases v with x | y
    · have hdeg : ((completeBipartiteGraph V W).neighborFinset (Sum.inl x)).card = m := by
        have h : (completeBipartiteGraph V W).neighborFinset (Sum.inl x) = Finset.univ.image Sum.inr := by
          ext (a | b)
          · simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj]
          · simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj]
        rw [h, Finset.card_image_of_injective _ Sum.inr_injective, Finset.card_univ, hW]
      rw [hdeg]
    · have hdeg : ((completeBipartiteGraph V W).neighborFinset (Sum.inr y)).card = m := by
        have h : (completeBipartiteGraph V W).neighborFinset (Sum.inr y) = Finset.univ.image Sum.inl := by
          ext (a | b)
          · simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj]
          · simp [SimpleGraph.mem_neighborFinset, completeBipartiteGraph_adj]
        rw [h, Finset.card_image_of_injective _ Sum.inl_injective, Finset.card_univ, hV]
      rw [hdeg]
  · intro x hx
    rw [SimpleGraph.mem_neighborFinset] at hx ⊢
    exact hH_sub hx
