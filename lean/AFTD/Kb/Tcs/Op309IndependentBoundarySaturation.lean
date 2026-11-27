import AFTD.Prelude

/-!
# op309_independent_boundary_saturation

Topic: graphs   Node: 4bc168aa7390

Provenance: helper lemma. Cubic equality boundary count for the OP-309 canonical port obstruction.

If an independent vertex set has pairwise disjoint incidence rows and the selected edges together with their degree sum account for every edge, every nonselected edge meets that independent set.
-/

theorem op309_independent_boundary_saturation
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (R : Finset (Sym2 V))
    (hR : R ⊆ G.edgeFinset)
    (hind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v)
    (hclean : ∀ e ∈ R, ∀ u ∈ U, u ∉ e)
    (hsum : G.edgeFinset.card = R.card + ∑ u ∈ U, G.degree u) :
    ∀ e ∈ G.edgeFinset, e ∉ R → ∃ u ∈ U, u ∈ e := by  classical
  let B : Finset (Sym2 V) := U.biUnion (fun v => G.incidenceFinset v)
  have hpair : (U : Set V).PairwiseDisjoint (fun v => G.incidenceFinset v) := by
    intro u hu v hv huv
    apply Finset.disjoint_left.mpr
    intro e heu hev
    apply hind u hu v hv
    exact G.adj_of_mem_incidenceSet huv ((G.mem_incidenceFinset u e).mp heu) ((G.mem_incidenceFinset v e).mp hev)
  have hBcard : B.card = ∑ u ∈ U, G.degree u := by
    simp only [B, Finset.card_biUnion hpair, G.card_incidenceFinset_eq_degree]
  have hdisj : Disjoint R B := by
    apply Finset.disjoint_left.mpr
    intro e he heB
    obtain ⟨u,hu,heu⟩ := Finset.mem_biUnion.mp heB
    exact hclean e he u hu ((G.mem_incidenceFinset u e).mp heu).2
  have hsub : R ∪ B ⊆ G.edgeFinset := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · exact hR he
    · obtain ⟨u,hu,heu⟩ := Finset.mem_biUnion.mp he
      exact G.incidenceFinset_subset u heu
  have hcard : (R ∪ B).card = G.edgeFinset.card := by
    rw [Finset.card_union_of_disjoint hdisj, hBcard, hsum]
  have heq : R ∪ B = G.edgeFinset := Finset.eq_of_subset_of_card_le hsub hcard.ge
  intro e he hnot
  have he' : e ∈ R ∪ B := heq.symm ▸ he
  have heB : e ∈ B := (Finset.mem_union.mp he').resolve_left hnot
  obtain ⟨u,hu,heu⟩ := Finset.mem_biUnion.mp heB
  exact ⟨u,hu,((G.mem_incidenceFinset u e).mp heu).2⟩
