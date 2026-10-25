import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphRichWitnessGraph

/-!
# simple_graph_rich_witness_graph_cubic_triangle_free_neighbors

Topic: graphs   Node: fafcdc998153

Provenance: helper lemma. Helper obstruction to the greedy proof route for OP-309. The witness graph is from arXiv:2610.16446, Section 2. This is a six-neighbor lower bound, not a five-color existence result.

In a finite triangle-free cubic graph, every vertex of a prescribed-witness graph has at least six neighbors whenever R totally dominates the line graph.
-/

theorem simple_graph_rich_witness_graph_cubic_triangle_free_neighbors
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (R : Set G.edgeSet)
    (hcubic : ∀ v, G.degree v = 3)
    (htriangle : ∀ u v w, G.Adj u v → G.Adj v w → ¬ G.Adj w u)
    (hR : ∀ e, ∃ r ∈ R, G.lineGraph.Adj e r) :
    ∀ e, 6 ≤ ((simple_graph_rich_witness_graph G R).neighborSet e).ncard := by
  classical
  intro e
  obtain ⟨r, hr, her⟩ := hR e
  obtain ⟨herne, v, hve, hvr⟩ := SimpleGraph.lineGraph_adj_iff_exists.mp her
  let u := Sym2.Mem.other hve
  let w := Sym2.Mem.other hvr
  have heval : e.val = s(v,u) := (Sym2.other_spec hve).symm
  have hrval : r.val = s(v,w) := (Sym2.other_spec hvr).symm
  have hvu : G.Adj v u := (SimpleGraph.mem_edgeSet G).mp (heval ▸ e.property)
  have hvw : G.Adj v w := (SimpleGraph.mem_edgeSet G).mp (hrval ▸ r.property)
  have huw : u ≠ w := by
    intro h
    apply herne
    apply Subtype.ext
    rw [heval, hrval, h]
  have hwu : ¬ G.Adj w u := htriangle u v w hvu.symm hvw
  have hU : ((G.neighborFinset u).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem (by simpa using hvu.symm),
      G.card_neighborFinset_eq_degree, hcubic]
  obtain ⟨p,q,hpq,hpqset⟩ := Finset.card_eq_two.mp hU
  have hp : p ≠ v ∧ G.Adj u p := by
    have hm : p ∈ (G.neighborFinset u).erase v := by rw [hpqset]; simp
    simpa using hm
  have hq : q ≠ v ∧ G.Adj u q := by
    have hm : q ∈ (G.neighborFinset u).erase v := by rw [hpqset]; simp
    simpa using hm
  have hW : ((G.neighborFinset w).erase v).card = 2 := by
    rw [Finset.card_erase_of_mem (by simpa using hvw.symm),
      G.card_neighborFinset_eq_degree, hcubic]
  obtain ⟨a,b,hab,habset⟩ := Finset.card_eq_two.mp hW
  have ha : a ≠ v ∧ G.Adj w a := by
    have hm : a ∈ (G.neighborFinset w).erase v := by rw [habset]; simp
    simpa using hm
  have hb : b ≠ v ∧ G.Adj w b := by
    have hm : b ∈ (G.neighborFinset w).erase v := by rw [habset]; simp
    simpa using hm
  have hV : (((G.neighborFinset v).erase u).erase w).card = 1 := by
    rw [Finset.card_erase_of_mem (by simp [huw.symm, hvw]),
      Finset.card_erase_of_mem (by simpa using hvu),
      G.card_neighborFinset_eq_degree, hcubic]
  obtain ⟨t,htset⟩ := Finset.card_eq_one.mp hV
  have ht : t ≠ w ∧ t ≠ u ∧ G.Adj v t := by
    have hm : t ∈ ((G.neighborFinset v).erase u).erase w := by rw [htset]; simp
    simpa [and_assoc] using hm
  have hau : a ≠ u := fun h => hwu (h ▸ ha.2)
  have hbu : b ≠ u := fun h => hwu (h ▸ hb.2)
  have hvune := hvu.ne
  have hvwne := hvw.ne
  have hupne := hp.2.ne
  have huqne := hq.2.ne
  have hwane := ha.2.ne
  have hwbne := hb.2.ne
  have hvtne := ht.2.2.ne
  let f₁ : G.edgeSet := ⟨s(u,p), (SimpleGraph.mem_edgeSet G).mpr hp.2⟩
  let f₂ : G.edgeSet := ⟨s(u,q), (SimpleGraph.mem_edgeSet G).mpr hq.2⟩
  let f₄ : G.edgeSet := ⟨s(v,t), (SimpleGraph.mem_edgeSet G).mpr ht.2.2⟩
  let f₅ : G.edgeSet := ⟨s(w,a), (SimpleGraph.mem_edgeSet G).mpr ha.2⟩
  let f₆ : G.edgeSet := ⟨s(w,b), (SimpleGraph.mem_edgeSet G).mpr hb.2⟩
  let fs : Fin 6 → G.edgeSet := ![f₁,f₂,r,f₄,f₅,f₆]
  have hene : ∀ i, e ≠ fs i := by
    intro i h
    have hv := congrArg Subtype.val h
    fin_cases i <;> dsimp [fs, f₁, f₂, f₄, f₅, f₆] at hv
    all_goals rw [heval] at hv
    all_goals simp only [hrval, Sym2.eq_iff] at hv
    all_goals grind only
  have hinj : Function.Injective fs := by
    intro i j h
    have hv := congrArg Subtype.val h
    fin_cases i <;> fin_cases j <;> first | rfl | skip
    all_goals dsimp [fs, f₁, f₂, f₄, f₅, f₆] at hv
    all_goals simp only [hrval, Sym2.eq_iff] at hv
    all_goals grind only
  have hline : ∀ i : Fin 4, G.lineGraph.Adj e (fs (i.castAdd 2)) := by
    intro i
    apply SimpleGraph.lineGraph_adj_iff_exists.mpr
    refine ⟨hene _, ?_⟩
    fin_cases i
    · exact ⟨u, by rw [heval]; simp, by simp [fs,f₁]⟩
    · exact ⟨u, by rw [heval]; simp, by simp [fs,f₂]⟩
    · exact ⟨v, by rw [heval]; simp, by simp [fs,hrval]⟩
    · exact ⟨v, by rw [heval]; simp, by simp [fs,f₄]⟩
  have hrline : ∀ i : Fin 2, G.lineGraph.Adj r (fs (i.addNat 4)) := by
    intro i
    apply SimpleGraph.lineGraph_adj_iff_exists.mpr
    refine ⟨?_, ?_⟩
    · intro h
      have hh : fs 2 = fs (i.addNat 4) := by simpa [fs] using h
      have hi := hinj hh
      have hnum := congrArg Fin.val hi
      change (2 : ℕ) = i.val + 4 at hnum
      omega
    · refine ⟨w, by rw [hrval]; simp, ?_⟩
      fin_cases i <;> simp [fs,f₅,f₆]
  have hneighbor : ∀ i, fs i ∈ (simple_graph_rich_witness_graph G R).neighborSet e := by
    intro i
    refine ⟨hene i, ?_⟩
    fin_cases i
    · exact Or.inl (hline 0)
    · exact Or.inl (hline 1)
    · exact Or.inl (hline 2)
    · exact Or.inl (hline 3)
    · exact Or.inr ⟨r, hr, her.symm, hrline 0⟩
    · exact Or.inr ⟨r, hr, her.symm, hrline 1⟩
  have hsub : (↑(Finset.univ.image fs) : Set G.edgeSet) ⊆
      (simple_graph_rich_witness_graph G R).neighborSet e := by
    intro f hf
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hf
    exact hneighbor i
  have hcard : (Finset.univ.image fs).card = 6 := by
    rw [Finset.card_image_of_injective _ hinj]
    rfl
  have := Set.ncard_le_ncard hsub
  rw [Set.ncard_coe_finset, hcard] at this
  exact this
