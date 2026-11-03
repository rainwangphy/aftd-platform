import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphSafe17Shift
import AFTD.Kb.Tcs.DigraphSafe17RootedTriangleUnsafe

/-!
# digraph_safe17_triangle_unsafe

Topic: graphs   Node: 8cba61fbb45c

Provenance: helper lemma. Finite safe-cycle obstruction for OP-110; experiment 13260.

Every directed triangle in the displayed graph has an outside vertex pointing to all three of its vertices.
-/

private instance in504_safe17_decAdj_5 : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_triangle_unsafe (u a b : Fin 17)
    (hua : digraph_safe17_graph.Adj u a) (hab : digraph_safe17_graph.Adj a b)
    (hbu : digraph_safe17_graph.Adj b u) :
    ∃ x : Fin 17, x ≠ u ∧ x ≠ a ∧ x ≠ b ∧
      digraph_safe17_graph.Adj x u ∧ digraph_safe17_graph.Adj x a ∧
      digraph_safe17_graph.Adj x b := by
  have hn (x y : Fin 17) : digraph_safe17_graph.Adj (x-u) (y-u) ↔
      digraph_safe17_graph.Adj x y := by
    simpa only [sub_eq_add_neg] using digraph_safe17_shift x y (-u)
  have h1 : digraph_safe17_graph.Adj 0 (a-u) := by simpa using (hn u a).2 hua
  have h2 := (hn a b).2 hab
  have h3 : digraph_safe17_graph.Adj (b-u) 0 := by simpa using (hn b u).2 hbu
  obtain ⟨x,hx0,hxa,hxb,hu,ha,hb⟩ := digraph_safe17_rooted_triangle_unsafe (a-u) (b-u) h1 h2 h3
  have hne (v : Fin 17) (hv : x ≠ v-u) : x+u ≠ v := by
    intro he
    apply hv
    have ht := congrArg (fun z : Fin 17 => z-u) he
    simpa using ht
  have back (v : Fin 17) (hv : digraph_safe17_graph.Adj x (v-u)) :
      digraph_safe17_graph.Adj (x+u) v := by
    simpa using (digraph_safe17_shift x (v-u) u).2 hv
  refine ⟨x+u,hne u (by simpa using hx0),hne a hxa,hne b hxb,?_,back a ha,back b hb⟩
  simpa using (digraph_safe17_shift x 0 u).2 hu
