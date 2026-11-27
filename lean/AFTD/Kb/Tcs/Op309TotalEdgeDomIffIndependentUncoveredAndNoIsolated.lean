import AFTD.Prelude

/-!
# op309_total_edge_dom_iff_independent_uncovered_and_no_isolated

Topic: graphs   Node: fdb4db6c6c84

Provenance: helper lemma. Uncovered-vertex characterization for the local P3 switch in OP-309.

An edge set totally dominates the edges of a simple graph exactly when its uncovered vertices are independent and every selected edge has a different selected edge sharing an endpoint.
-/

theorem op309_total_edge_dom_iff_independent_uncovered_and_no_isolated
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (R : Finset G.edgeSet) :
    (∀ e : G.edgeSet, ∃ f ∈ R, G.lineGraph.Adj e f) ↔
    (∀ a b : V, (∀ f ∈ R, a ∉ f.1) → (∀ f ∈ R, b ∉ f.1) → ¬ G.Adj a b) ∧
    (∀ e ∈ R, ∃ f ∈ R, G.lineGraph.Adj e f) := by
  classical
  constructor
  · intro hdom
    constructor
    · intro a b ha hb hab
      let e : G.edgeSet := ⟨s(a,b), (G.mem_edgeSet).mpr hab⟩
      obtain ⟨f,hf,hef⟩ := hdom e
      obtain ⟨w,hw,hwf⟩ := (SimpleGraph.lineGraph_adj_iff_exists.mp hef).2
      have hw' : w = a ∨ w = b := by simpa [e, Sym2.mem_iff] using hw
      rcases hw' with rfl | rfl
      · exact ha f hf hwf
      · exact hb f hf hwf
    · intro e he
      exact hdom e
  · rintro ⟨hind,hselected⟩ e
    by_cases he : e ∈ R
    · exact hselected e he
    · have hpair : ∃ a b : V, e.1 = s(a,b) := by
        refine Sym2.ind (fun a b => ?_) e.1
        exact ⟨a,b,rfl⟩
      obtain ⟨a,b,hab⟩ := hpair
      have hadj : G.Adj a b := (G.mem_edgeSet).mp (hab ▸ e.2)
      by_cases ha : ∃ f ∈ R, a ∈ f.1
      · obtain ⟨f,hf,haf⟩ := ha
        refine ⟨f,hf,SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨?_,a,?_,haf⟩⟩
        · intro h
          exact he (h ▸ hf)
        · rw [hab]
          simp
      · have hb : ∃ f ∈ R, b ∈ f.1 := by
          by_contra hb
          apply hind a b ?_ ?_ hadj
          · intro f hf haf
            exact ha ⟨f,hf,haf⟩
          · intro f hf hbf
            exact hb ⟨f,hf,hbf⟩
        obtain ⟨f,hf,hbf⟩ := hb
        refine ⟨f,hf,SimpleGraph.lineGraph_adj_iff_exists.mpr ⟨?_,b,?_,hbf⟩⟩
        · intro h
          exact he (h ▸ hf)
        · rw [hab]
          simp
