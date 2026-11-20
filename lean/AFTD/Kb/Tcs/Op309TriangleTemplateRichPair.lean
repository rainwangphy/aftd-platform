import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_triangle_template_rich_pair

Topic: graphs   Node: 52850d943587

Provenance: helper lemma. Local triangle template for the claw-free cubic route to OP-309; checked in experiments 31379, 31384, and 31393.

For a triangle with exactly the displayed neighbor sets, if its three internal edges receive colors 2, 3, 4 and its external ports receive 0, 0, 1, then the two triangle edges incident with the third vertex are rich.
-/

theorem op309_tri_tmpl_adj_cases {V : Type*} (G : SimpleGraph V) (e f : G.edgeSet) (p q : V)
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

theorem op309_tri_tmpl_rich_of_four {V : Type*} (G : SimpleGraph V) (c : G.edgeSet → Fin 5)
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

theorem op309_triangle_template_rich_pair
    {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (u v w x y z : V) (hdist : [u,v,w].Nodup)
    (hx : x ∉ [u,v,w]) (hy : y ∉ [u,v,w]) (hz : z ∉ [u,v,w])
    (hu : ∀ t, G.Adj u t ↔ t = v ∨ t = w ∨ t = x)
    (hv : ∀ t, G.Adj v t ↔ t = u ∨ t = w ∨ t = y)
    (hw : ∀ t, G.Adj w t ↔ t = u ∨ t = v ∨ t = z)
    (c : G.edgeSet → Fin 5)
    (h0 : ∀ e : G.edgeSet, e.1 = s(u,v) → c e = 2)
    (h1 : ∀ e : G.edgeSet, e.1 = s(u,w) → c e = 3)
    (h2 : ∀ e : G.edgeSet, e.1 = s(v,w) → c e = 4)
    (h3 : ∀ e : G.edgeSet, e.1 = s(u,x) → c e = 0)
    (h4 : ∀ e : G.edgeSet, e.1 = s(v,y) → c e = 0)
    (h5 : ∀ e : G.edgeSet, e.1 = s(w,z) → c e = 1) :
    (∀ e : G.edgeSet, e.1 = s(u,w) → simple_graph_edge_is_rich G c e) ∧
    (∀ e : G.edgeSet, e.1 = s(v,w) → simple_graph_edge_is_rich G c e) := by
  constructor
  · intro e he
    refine op309_tri_tmpl_rich_of_four G c e s(u,v) s(u,x) s(v,w) s(w,z) 2 0 4 1 (by decide) ?_
    intro f hf
    obtain ⟨t, ⟨ht, htq, hft⟩ | ⟨ht, htq, hft⟩⟩ := op309_tri_tmpl_adj_cases G e f u w he hf
    · rcases (hu t).mp ht with h | h | h <;> subst t
      · exact Or.inl ⟨hft, h0 f hft⟩
      · exact absurd rfl htq
      · exact Or.inr (Or.inl ⟨hft, h3 f hft⟩)
    · rcases (hw t).mp ht with h | h | h <;> subst t
      · exact absurd rfl htq
      · have : (f : Sym2 V) = s(v, w) := hft.trans Sym2.eq_swap
        exact Or.inr (Or.inr (Or.inl ⟨this, h2 f this⟩))
      · exact Or.inr (Or.inr (Or.inr ⟨hft, h5 f hft⟩))
  · intro e he
    refine op309_tri_tmpl_rich_of_four G c e s(u,v) s(v,y) s(u,w) s(w,z) 2 0 3 1 (by decide) ?_
    intro f hf
    obtain ⟨t, ⟨ht, htq, hft⟩ | ⟨ht, htq, hft⟩⟩ := op309_tri_tmpl_adj_cases G e f v w he hf
    · rcases (hv t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, v) := hft.trans Sym2.eq_swap
        exact Or.inl ⟨this, h0 f this⟩
      · exact absurd rfl htq
      · exact Or.inr (Or.inl ⟨hft, h4 f hft⟩)
    · rcases (hw t).mp ht with h | h | h <;> subst t
      · have : (f : Sym2 V) = s(u, w) := hft.trans Sym2.eq_swap
        exact Or.inr (Or.inr (Or.inl ⟨this, h1 f this⟩))
      · exact absurd rfl htq
      · exact Or.inr (Or.inr (Or.inr ⟨hft, h5 f hft⟩))
