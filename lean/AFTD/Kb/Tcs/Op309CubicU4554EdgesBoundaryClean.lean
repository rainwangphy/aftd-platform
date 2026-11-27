import AFTD.Prelude
import AFTD.Kb.Tcs.Op309IndependentBoundarySaturation

/-!
# op309_cubic_u45_54_edges_boundary_clean

Topic: graphs   Node: 15b5ad205532

Provenance: helper lemma. Cubic equality boundary count for the OP-309 canonical port obstruction.

In a 126-vertex cubic graph, a totally edge-dominating 54-edge set leaving 45 vertices uncovered has every nonselected edge incident to an uncovered vertex.
-/

theorem op309_cubic_u45_54_edges_boundary_clean
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hreg : ∀ v, G.degree v = 3) (hn : Fintype.card V = 126)
    (R : Finset G.edgeSet) (hR : R.card = 54)
    (hdom : ∀ e : G.edgeSet, ∃ f ∈ R, G.lineGraph.Adj e f)
    (hU : ((Finset.univ : Finset V).filter fun u => ∀ e ∈ R, u ∉ e.1).card = 45) :
    ∀ e : G.edgeSet, e ∉ R → ∃ u : V, u ∈ e.1 ∧ ∀ f ∈ R, u ∉ f.1 := by  classical
  let U := (Finset.univ : Finset V).filter fun u => ∀ e ∈ R, u ∉ e.1
  let S := R.image Subtype.val
  have hS : S ⊆ G.edgeFinset := by
    intro e he
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact SimpleGraph.mem_edgeFinset.mpr f.2
  have hind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v := by
    intro u hu v hv huv
    let e : G.edgeSet := ⟨s(u,v), (G.mem_edgeSet).mpr huv⟩
    obtain ⟨f,hf,hef⟩ := hdom e
    obtain ⟨w,hw,hwf⟩ := (SimpleGraph.lineGraph_adj_iff_exists.mp hef).2
    have hw' : w = u ∨ w = v := by simpa [e, Sym2.mem_iff] using hw
    rcases hw' with rfl | rfl
    · exact (Finset.mem_filter.mp hu).2 f hf hwf
    · exact (Finset.mem_filter.mp hv).2 f hf hwf
  have hclean : ∀ e ∈ S, ∀ u ∈ U, u ∉ e := by
    intro e he u hu
    obtain ⟨f,hf,rfl⟩ := Finset.mem_image.mp he
    exact (Finset.mem_filter.mp hu).2 f hf
  have hcS : S.card = R.card := by
    exact Finset.card_image_iff.mpr (fun _ _ _ _ h => Subtype.ext h)
  have hecount : G.edgeFinset.card = 189 := by
    have h := G.sum_degrees_eq_twice_card_edges
    simp_rw [hreg] at h
    simp only [Finset.sum_const_zero, Finset.sum_const, Finset.card_univ, hn,
      nsmul_eq_mul] at h
    omega
  have hsum : G.edgeFinset.card = S.card + ∑ u ∈ U, G.degree u := by
    have hUcard : U.card = 45 := hU
    simp [hecount, hcS, hR, hreg, hUcard]
  intro e he
  have heS : e.1 ∉ S := by
    intro heS
    obtain ⟨f,hf,hfe⟩ := Finset.mem_image.mp heS
    exact he (Subtype.ext hfe ▸ hf)
  obtain ⟨u,hu,hue⟩ := op309_independent_boundary_saturation G U S hS hind hclean hsum e.1
    (SimpleGraph.mem_edgeFinset.mpr e.2) heS
  exact ⟨u,hue,(Finset.mem_filter.mp hu).2⟩
