import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphSafe17Shift
import AFTD.Kb.Tcs.DigraphSafe17RootedFourUnsafe

/-!
# digraph_safe17_four_unsafe

Topic: graphs   Node: a88089418d1e

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

Every directed four-cycle in the displayed graph has an outside vertex pointing to at least three of its vertices.
-/

private instance in504_safe17_decAdj_6 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_four_unsafe (u a b c : Fin 17)
    (hua : digraph_safe17_graph.Adj u a) (hab : digraph_safe17_graph.Adj a b)
    (hbc : digraph_safe17_graph.Adj b c) (hcu : digraph_safe17_graph.Adj c u) :
    ∃ x : Fin 17, x ≠ u ∧ x ≠ a ∧ x ≠ b ∧ x ≠ c ∧
      ((digraph_safe17_graph.Adj x u ∧ digraph_safe17_graph.Adj x a ∧ digraph_safe17_graph.Adj x b) ∨
       (digraph_safe17_graph.Adj x u ∧ digraph_safe17_graph.Adj x a ∧ digraph_safe17_graph.Adj x c) ∨
       (digraph_safe17_graph.Adj x u ∧ digraph_safe17_graph.Adj x b ∧ digraph_safe17_graph.Adj x c) ∨
       (digraph_safe17_graph.Adj x a ∧ digraph_safe17_graph.Adj x b ∧ digraph_safe17_graph.Adj x c)) := by
  have hn (x y : Fin 17) : digraph_safe17_graph.Adj (x-u) (y-u) ↔
      digraph_safe17_graph.Adj x y := by
    simpa only [sub_eq_add_neg] using digraph_safe17_shift x y (-u)
  have h1 : digraph_safe17_graph.Adj 0 (a-u) := by simpa using (hn u a).2 hua
  have h2 := (hn a b).2 hab
  have h3 := (hn b c).2 hbc
  have h4 : digraph_safe17_graph.Adj (c-u) 0 := by simpa using (hn c u).2 hcu
  obtain ⟨x,hx0,hxa,hxb,hxc,htrip⟩ := digraph_safe17_rooted_four_unsafe (a-u) (b-u) (c-u) h1 h2 h3 h4
  have hne (v : Fin 17) (hv : x ≠ v-u) : x+u ≠ v := by
    intro he
    apply hv
    have ht := congrArg (fun z : Fin 17 => z-u) he
    simpa using ht
  have hxu : x+u ≠ u := hne u (by simpa using hx0)
  have back (v : Fin 17) (hv : digraph_safe17_graph.Adj x (v-u)) :
      digraph_safe17_graph.Adj (x+u) v := by
    simpa using (digraph_safe17_shift x (v-u) u).2 hv
  have back0 (hv : digraph_safe17_graph.Adj x 0) : digraph_safe17_graph.Adj (x+u) u := by
    simpa using (digraph_safe17_shift x 0 u).2 hv
  refine ⟨x+u,hxu,hne a hxa,hne b hxb,hne c hxc,?_⟩
  rcases htrip with h | h | h | h
  · exact Or.inl ⟨back0 h.1,back a h.2.1,back b h.2.2⟩
  · exact Or.inr (Or.inl ⟨back0 h.1,back a h.2.1,back c h.2.2⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨back0 h.1,back b h.2.1,back c h.2.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨back a h.1,back b h.2.1,back c h.2.2⟩))
