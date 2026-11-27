import AFTD.Prelude
import AFTD.Kb.Tcs.Op309CanonicalPaddedPortClasses
import AFTD.Kb.Tcs.Op309SelectedEdgeGraph
import AFTD.Kb.GameTheoryEconomics.ArenaReachableTrans

/-!
# op309_canonical_clean_component_class_confined

Topic: graphs   Node: 916cc084a186

Provenance: helper lemma. OP-309 canonical-port high-girth clean-component argument.

If every outside edge meeting a selected component also has an uncovered endpoint, canonical port equalities cannot propagate from an outside edge meeting that component to an edge that misses it.
-/

theorem op309_canonical_clean_component_class_confined
    {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet)
    (q : Sum G.edgeSet (V × Fin 3) → A)
    (hq : op309_canonical_padded_port_classes G R q)
    (v : V) (hv : ∃ e ∈ R, v ∈ e.1)
    (hclean : ∀ z : G.edgeSet, z ∉ R →
      (∃ a : V, a ∈ z.1 ∧ (op309_selected_edge_graph G R).Reachable v a) →
      ∃ u : V, u ∈ z.1 ∧ ∀ e ∈ R, u ∉ e.1)
    (e f : G.edgeSet) (he : e ∉ R) (hf : f ∉ R)
    (heC : ∃ a : V, a ∈ e.1 ∧ (op309_selected_edge_graph G R).Reachable v a)
    (heq : q (.inl e) = q (.inl f)) :
    ∃ a : V, a ∈ f.1 ∧ (op309_selected_edge_graph G R).Reachable v a := by
  classical
  let H := op309_selected_edge_graph G R
  have hcov : ∀ x : V, H.Reachable v x → ∃ g ∈ R, x ∈ g.1 := by
    intro x hx
    by_cases h : x = v
    · subst x
      exact hv
    · have hne : v ≠ x := Ne.symm h
      obtain ⟨w, hw⟩ := hx.nonempty_neighborSet_right hne
      have hm : s(x,w) ∈ R.image Subtype.val := by
        change (SimpleGraph.fromEdgeSet (↑(R.image Subtype.val) : Set (Sym2 V))).Adj x w at hw
        exact ((SimpleGraph.fromEdgeSet_adj _).mp hw).1
      obtain ⟨g, hg, hgw⟩ := Finset.mem_image.mp hm
      refine ⟨g, hg, ?_⟩
      rw [hgw]
      simp
  have hstay (z : G.edgeSet) (hz : z ∉ R)
      (hm : ∃ a : V, a ∈ z.1 ∧ H.Reachable v a)
      (x : V) (hx : x ∈ z.1) (hxc : ∃ g ∈ R, x ∈ g.1) : H.Reachable v x := by
    obtain ⟨a, ha, hva⟩ := hm
    obtain ⟨u, hu, hu0⟩ := hclean z hz ⟨a, ha, hva⟩
    have hxu : x ≠ u := by
      intro h
      subst x
      obtain ⟨g, hg, hxg⟩ := hxc
      exact hu0 g hg hxg
    have hau : a ≠ u := by
      intro h
      subst a
      obtain ⟨g, hg, hug⟩ := hcov u hva
      exact hu0 g hg hug
    obtain ⟨y, hy⟩ := Sym2.mem_iff_exists.mp ha
    rw [hy, Sym2.mem_iff] at hu hx
    rcases hu with hua | huy
    · exact False.elim (hau hua.symm)
    · rcases hx with hxa | hxy
      · simpa [hxa] using hva
      · exact False.elim (hxu (hxy.trans huy.symm))
  have hc := hq e f he hf heq
  clear hf heq hq
  induction hc with
  | refl => exact heC
  | tail hxy hyz ih =>
    rcases hyz with ⟨hy, hz, hyzq, a, b, hay, hbz, hac, hbc, hab⟩
    have hca : ∃ g ∈ R, a ∈ g.1 := by
      obtain ⟨g, hg⟩ := hac
      exact ⟨g, (Finset.mem_filter.mp hg).1, (Finset.mem_filter.mp hg).2⟩
    have hva : H.Reachable v a := hstay _ hy ih a hay hca
    exact ⟨b, hbz, hva.trans hab⟩
