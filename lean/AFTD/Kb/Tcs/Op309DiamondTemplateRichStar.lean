import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_diamond_template_rich_star

Topic: graphs   Node: 93d5b53958da

Provenance: helper lemma. Local diamond template for the claw-free cubic route to OP-309; checked by finite enumeration in experiment 31385.

For a diamond with exactly the displayed neighbor sets and displayed five-color edge labels, its central edge and the two edges from the second central vertex form a rich star.
-/

theorem op309_dia_tmpl_adj_cases {V : Type*} (G : SimpleGraph V) (e f : G.edgeSet) (p q : V)
    (he : (e : Sym2 V) = s(p, q)) (hadj : G.lineGraph.Adj e f) :
    ∃ t, (G.Adj p t ∧ t ≠ q ∧ (f : Sym2 V) = s(p, t)) ∨
         (G.Adj q t ∧ t ≠ p ∧ (f : Sym2 V) = s(q, t)) := by
  rw [SimpleGraph.lineGraph_adj_iff_exists] at hadj
  obtain ⟨hne, y, hye, hyf⟩ := hadj
  rw [he, Sym2.mem_iff] at hye
  obtain ⟨t, ht⟩ := Sym2.mem_iff_exists.mp hyf
  have hft : G.Adj y t := by
    have := f.2; rw [ht] at this; exact (SimpleGraph.mem_edgeSet G).mp this
  refine ⟨t, ?_⟩
  rcases hye with rfl | rfl
  · left
    refine ⟨hft, ?_, ht⟩
    rintro rfl; exact hne (Subtype.ext (he.trans ht.symm))
  · right
    refine ⟨hft, ?_, ht⟩
    rintro rfl; exact hne (Subtype.ext (he.trans (ht.trans Sym2.eq_swap).symm))

theorem op309_dia_tmpl_rich_of_four {V : Type*} (G : SimpleGraph V) (c : G.edgeSet → Fin 5)
    (e : G.edgeSet) (A B C D : Sym2 V) (a b c' d : Fin 5)
    (hdist : a ≠ b ∧ a ≠ c' ∧ a ≠ d ∧ b ≠ c' ∧ b ≠ d ∧ c' ≠ d)
    (h : ∀ f, G.lineGraph.Adj e f →
      ((f : Sym2 V) = A ∧ c f = a) ∨ ((f : Sym2 V) = B ∧ c f = b) ∨
      ((f : Sym2 V) = C ∧ c f = c') ∨ ((f : Sym2 V) = D ∧ c f = d)) :
    simple_graph_edge_is_rich G c e := by
  intro f f2 hf hg hfg hc
  obtain ⟨d1, d2, d3, d4, d5, d6⟩ := hdist
  rcases h f hf with ⟨fA, fa⟩ | ⟨fA, fa⟩ | ⟨fA, fa⟩ | ⟨fA, fa⟩ <;>
  rcases h f2 hg with ⟨gA, ga⟩ | ⟨gA, ga⟩ | ⟨gA, ga⟩ | ⟨gA, ga⟩ <;>
  first
    | exact hfg (Subtype.ext (fA.trans gA.symm))
    | (rw [fa, ga] at hc; first | exact absurd hc ‹_› | exact absurd hc.symm ‹_›)

theorem op309_diamond_template_rich_star
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (u v a b x y : V) (hdist : [u,v,a,b].Nodup)
    (hx : x ∉ [u,v,a,b]) (hy : y ∉ [u,v,a,b])
    (hu : ∀ w, G.Adj u w ↔ w = v ∨ w = a ∨ w = b)
    (hv : ∀ w, G.Adj v w ↔ w = u ∨ w = a ∨ w = b)
    (ha : ∀ w, G.Adj a w ↔ w = u ∨ w = v ∨ w = x)
    (hb : ∀ w, G.Adj b w ↔ w = u ∨ w = v ∨ w = y)
    (c : G.edgeSet → Fin 5)
    (h0 : ∀ e : G.edgeSet, e.1 = s(u,v) → c e = 2)
    (h1 : ∀ e : G.edgeSet, e.1 = s(u,a) → c e = 1)
    (h2 : ∀ e : G.edgeSet, e.1 = s(u,b) → c e = 0)
    (h3 : ∀ e : G.edgeSet, e.1 = s(v,a) → c e = 3)
    (h4 : ∀ e : G.edgeSet, e.1 = s(v,b) → c e = 4)
    (h5 : ∀ e : G.edgeSet, e.1 = s(a,x) → c e = 0)
    (h6 : ∀ e : G.edgeSet, e.1 = s(b,y) → c e = 1) :
    (∀ e : G.edgeSet, e.1 = s(u,v) → simple_graph_edge_is_rich G c e) ∧
    (∀ e : G.edgeSet, e.1 = s(v,a) → simple_graph_edge_is_rich G c e) ∧
    (∀ e : G.edgeSet, e.1 = s(v,b) → simple_graph_edge_is_rich G c e) := by
  refine ⟨?_, ?_, ?_⟩
  · intro e he
    refine op309_dia_tmpl_rich_of_four G c e s(u,a) s(u,b) s(v,a) s(v,b) 1 0 3 4 (by decide) ?_
    intro f hf
    obtain ⟨t, ⟨ht, htq, hft⟩ | ⟨ht, htq, hft⟩⟩ := op309_dia_tmpl_adj_cases G e f u v he hf
    · rcases (hu t).mp ht with h | h | h <;> subst t
      · exact absurd rfl htq
      · exact Or.inl ⟨hft, h1 f hft⟩
      · exact Or.inr (Or.inl ⟨hft, h2 f hft⟩)
    · rcases (hv t).mp ht with h | h | h <;> subst t
      · exact absurd rfl htq
      · exact Or.inr (Or.inr (Or.inl ⟨hft, h3 f hft⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hft, h4 f hft⟩))
  · intro e he
    refine op309_dia_tmpl_rich_of_four G c e s(u,v) s(v,b) s(u,a) s(a,x) 2 4 1 0 (by decide) ?_
    intro f hf
    obtain ⟨t, ⟨ht, htq, hft⟩ | ⟨ht, htq, hft⟩⟩ := op309_dia_tmpl_adj_cases G e f v a he hf
    · rcases (hv t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, v) := hft.trans Sym2.eq_swap
        exact Or.inl ⟨this, h0 f this⟩
      · exact absurd rfl htq
      · exact Or.inr (Or.inl ⟨hft, h4 f hft⟩)
    · rcases (ha t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, a) := hft.trans Sym2.eq_swap
        exact Or.inr (Or.inr (Or.inl ⟨this, h1 f this⟩))
      · exact absurd rfl htq
      · exact Or.inr (Or.inr (Or.inr ⟨hft, h5 f hft⟩))
  · intro e he
    refine op309_dia_tmpl_rich_of_four G c e s(u,v) s(v,a) s(u,b) s(b,y) 2 3 0 1 (by decide) ?_
    intro f hf
    obtain ⟨t, ⟨ht, htq, hft⟩ | ⟨ht, htq, hft⟩⟩ := op309_dia_tmpl_adj_cases G e f v b he hf
    · rcases (hv t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, v) := hft.trans Sym2.eq_swap
        exact Or.inl ⟨this, h0 f this⟩
      · exact Or.inr (Or.inl ⟨hft, h3 f hft⟩)
      · exact absurd rfl htq
    · rcases (hb t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, b) := hft.trans Sym2.eq_swap
        exact Or.inr (Or.inr (Or.inl ⟨this, h2 f this⟩))
      · exact absurd rfl htq
      · exact Or.inr (Or.inr (Or.inr ⟨hft, h6 f hft⟩))
