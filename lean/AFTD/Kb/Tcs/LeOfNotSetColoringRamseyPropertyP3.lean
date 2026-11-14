import AFTD.Prelude
import AFTD.Kb.Tcs.SetColoringRamseyProperty
import AFTD.Kb.Tcs.SupportGraph
import AFTD.Kb.Tcs.Order
import AFTD.Kb.Tcs.Support

/-!
# le_of_not_set_coloring_ramsey_property_p3

Topic: combinatorics   Node: 83631eac36f4

Provenance: helper lemma. arXiv:2611.15376 Lemma 2.1

If there exists an (a, b)-set-coloring of the complete graph K_N without a monochromatic two-edge path P_3 in any single color, then b * (N choose 2) ≤ a * ⌊N / 2⌋.
-/

private lemma le_of_not_set_coloring_ramsey_property_p3_isContained_of_adj_adj
    {V : Type*} {G : SimpleGraph V} {u v w : V}
    (huv : G.Adj u v) (hvw : G.Adj v w) (huw : u ≠ w) :
    (SimpleGraph.pathGraph 3).IsContained G := by
  classical
  have hp : (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    simp [SimpleGraph.Walk.support, huv.ne, hvw.ne, huw]
  have hlen : (SimpleGraph.Walk.cons huv (SimpleGraph.Walk.cons hvw SimpleGraph.Walk.nil)).length + 1 = 3 := rfl
  rw [← hlen]
  exact hp.isContained_pathGraph

private lemma le_of_not_set_coloring_ramsey_property_p3_maxDegree_le_one
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : ¬ (SimpleGraph.pathGraph 3).IsContained G) : G.maxDegree ≤ 1 := by
  classical
  by_contra hlt
  push Not at hlt
  have hne : Nonempty V := by
    by_contra he
    rw [not_nonempty_iff] at he
    haveI : IsEmpty V := he
    have h0 : G.maxDegree = 0 := by simp
    omega
  obtain ⟨v, hv⟩ := G.exists_maximal_degree_vertex
  have hdeg : 2 ≤ G.degree v := by omega
  rw [SimpleGraph.degree] at hdeg
  have h1 : 1 < (G.neighborFinset v).card := by omega
  obtain ⟨u, hu, w, hw, huw⟩ := Finset.one_lt_card.mp h1
  have huv : G.Adj u v := ((G.mem_neighborFinset v u).mp hu).symm
  have hvw : G.Adj v w := (G.mem_neighborFinset v w).mp hw
  exact h (le_of_not_set_coloring_ramsey_property_p3_isContained_of_adj_adj huv hvw huw)

private lemma le_of_not_set_coloring_ramsey_property_p3_card_edgeFinset_le_half
    {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (h : G.maxDegree ≤ 1) : G.edgeFinset.card ≤ Fintype.card V / 2 := by
  classical
  have hsum : ∑ v, G.degree v ≤ Fintype.card V := by
    calc ∑ v, G.degree v ≤ ∑ v, (1 : ℕ) := by
          apply Finset.sum_le_sum
          intro v _
          have := G.degree_le_maxDegree v
          omega
      _ = Fintype.card V := by simp
  have h2 := G.sum_degrees_eq_twice_card_edges
  rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 2)]
  omega

/-- An (a,b)-set-coloring of K_N avoiding monochromatic P_3 satisfies b * choose(N, 2) ≤ a * ⌊N/2⌋. -/
theorem le_of_not_set_coloring_ramsey_property_p3 (a b N : ℕ)
    (h : ¬ set_coloring_ramsey_property (SimpleGraph.pathGraph 3) a b 1 N) :
    b * N.choose 2 ≤ a * (N / 2) := by
  classical
  rw [set_coloring_ramsey_property] at h
  push Not at h
  obtain ⟨ϕ, hϕcard, hϕavoid⟩ := h
  let E := (⊤ : SimpleGraph (Fin N)).edgeSet
  have hsupp : ∀ c : Fin a, (support_graph ϕ {c}).edgeFinset.card =
      (Finset.univ.filter (fun e : E => c ∈ ϕ e)).card := by
    intro c
    have hle : support_graph ϕ {c} ≤ (⊤ : SimpleGraph (Fin N)) := le_top
    have hsupp' : (support_graph ϕ {c}).edgeSet =
        {e : Sym2 (Fin N) | ∃ h : e ∈ (⊤ : SimpleGraph (Fin N)).edgeSet, {c} ⊆ ϕ ⟨e, h⟩} \ Sym2.diagSet :=
      SimpleGraph.edgeSet_fromEdgeSet _
    let f : (support_graph ϕ {c}).edgeSet → {e : E // c ∈ ϕ e} := fun x =>
      ⟨⟨x.1, SimpleGraph.edgeSet_mono hle x.2⟩, by
        have hx' : (x.1 : Sym2 (Fin N)) ∈
            {e : Sym2 (Fin N) | ∃ h : e ∈ (⊤ : SimpleGraph (Fin N)).edgeSet, {c} ⊆ ϕ ⟨e, h⟩} \ Sym2.diagSet :=
          hsupp' ▸ x.2
        obtain ⟨⟨h, hsub⟩, _⟩ := hx'
        have hmem : c ∈ ϕ ⟨x.1, h⟩ := Finset.singleton_subset_iff.mp hsub
        convert hmem using 2⟩
    let g : {e : E // c ∈ ϕ e} → (support_graph ϕ {c}).edgeSet := fun y =>
      ⟨y.1.1, by
        have hmem : (y.1.1 : Sym2 (Fin N)) ∈
            {e : Sym2 (Fin N) | ∃ h : e ∈ (⊤ : SimpleGraph (Fin N)).edgeSet, {c} ⊆ ϕ ⟨e, h⟩} \ Sym2.diagSet := by
          refine ⟨⟨y.1.2, ?_⟩, ?_⟩
          · exact Finset.singleton_subset_iff.mpr y.2
          · have hy : (y.1.1 : Sym2 (Fin N)) ∈ Sym2.diagSetᶜ := by
              simpa [E, SimpleGraph.edgeSet_top] using y.1.2
            exact hy
        exact hsupp'.symm ▸ hmem⟩
    have hfg : Function.LeftInverse g f := by intro x; exact Subtype.ext rfl
    have hgf : Function.RightInverse g f := by intro y; exact Subtype.ext rfl
    have heq : Fintype.card (support_graph ϕ {c}).edgeSet = Fintype.card {e : E // c ∈ ϕ e} :=
      Fintype.card_congr ⟨f, g, hfg, hgf⟩
    calc (support_graph ϕ {c}).edgeFinset.card
        = Fintype.card (support_graph ϕ {c}).edgeSet := Set.toFinset_card _
      _ = Fintype.card {e : E // c ∈ ϕ e} := heq
      _ = (Finset.univ.filter (fun e : E => c ∈ ϕ e)).card := Fintype.card_subtype _
  have hdouble : ∑ c : Fin a, (support_graph ϕ {c}).edgeFinset.card = b * N.choose 2 := by
    simp only [hsupp]
    calc ∑ c : Fin a, (Finset.univ.filter (fun e : E => c ∈ ϕ e)).card
        = ∑ c : Fin a, ∑ e : E, (if c ∈ ϕ e then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro c _
            rw [Finset.card_filter]
      _ = ∑ e : E, ∑ c : Fin a, (if c ∈ ϕ e then 1 else 0) := Finset.sum_comm
      _ = ∑ e : E, (ϕ e).card := by
            apply Finset.sum_congr rfl
            intro e _
            rw [← Finset.card_filter]
            simp
      _ = ∑ e : E, b := by simp [hϕcard]
      _ = Fintype.card E * b := by simp
      _ = N.choose 2 * b := by
            congr 1
            have hE : Fintype.card E = (⊤ : SimpleGraph (Fin N)).edgeFinset.card :=
              (Set.toFinset_card E).symm
            rw [hE, SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
            simp
      _ = b * N.choose 2 := by ring
  have hle_each : ∀ c : Fin a, (support_graph ϕ {c}).edgeFinset.card ≤ N / 2 := by
    intro c
    have hnot : ¬ (SimpleGraph.pathGraph 3).IsContained (support_graph ϕ {c}) := by
      rw [SimpleGraph.IsContained]
      exact not_nonempty_iff.mpr (hϕavoid {c} (by simp))
    have hmax : (support_graph ϕ {c}).maxDegree ≤ 1 :=
      le_of_not_set_coloring_ramsey_property_p3_maxDegree_le_one _ hnot
    have hedge := le_of_not_set_coloring_ramsey_property_p3_card_edgeFinset_le_half _ hmax
    simpa using hedge
  calc b * N.choose 2 = ∑ c : Fin a, (support_graph ϕ {c}).edgeFinset.card := hdouble.symm
    _ ≤ ∑ c : Fin a, N / 2 := Finset.sum_le_sum (fun c _ => hle_each c)
    _ = a * (N / 2) := by simp
