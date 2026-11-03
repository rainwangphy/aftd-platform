import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphSafe17Graph
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSafe17Structure
import AFTD.Kb.Tcs.DigraphSafe17TriangleUnsafe
import AFTD.Kb.Tcs.DigraphSafe17FourUnsafe
import AFTD.Kb.Tcs.DigraphOrientedSafeSetIndegreeBound
import AFTD.Kb.Tcs.DigraphSafe17NoLongSafeSet
import AFTD.Kb.Tcs.DigraphSafe17TwoCycleImpossible
import AFTD.Kb.Tcs.DigraphSafe17TriangleCycleUnsafe
import AFTD.Kb.Tcs.DigraphSafe17FourCycleUnsafe

/-!
# digraph_safe17_every_proper_cycle_unsafe

Topic: graphs   Node: 8dadee24e64f

Provenance: helper lemma. Safe-cycle obstruction for OP-110; experiment 13260.

Every proper directed cycle in the displayed seventeen-vertex graph has an outside vertex with at least three outneighbors on it.
-/

private instance in504_safe17_decAdj_full : DecidableRel digraph_safe17_graph.Adj := by
  intro u v
  unfold digraph_safe17_graph
  infer_instance

theorem digraph_safe17_every_proper_cycle_unsafe
    (C : Finset (Fin 17)) (hcycle : digraph_directed_cycle_on digraph_safe17_graph C)
    (hproper : C ≠ Finset.univ) :
    ∃ v ∉ C, 3 ≤ (C.filter fun w => digraph_safe17_graph.Adj v w).card := by
  classical
  by_contra h
  have hsafe : ∀ v ∉ C, (C.filter fun w => digraph_safe17_graph.Adj v w).card ≤ 2 := by
    intro v hv
    by_contra hn
    exact h ⟨v,hv,by omega⟩
  have hne : ∃ v, v ∉ C := by
    by_contra hn
    apply hproper
    ext v
    simp only [Finset.mem_univ, iff_true]
    by_contra hv
    exact hn ⟨v,hv⟩
  have hmin : 2 ≤ C.card := by
    obtain ⟨l,hn,hlen,hset,_,_⟩ := hcycle
    have hc := List.toFinset_card_of_nodup hn
    rw [hset] at hc
    omega
  by_cases hlarge : 5 ≤ C.card
  · exact digraph_safe17_no_long_safe_set C hne hlarge hsafe
  · have hcases : C.card = 2 ∨ C.card = 3 ∨ C.card = 4 := by omega
    rcases hcases with h2 | h3 | h4
    · exact digraph_safe17_two_cycle_impossible C hcycle h2
    · exact digraph_safe17_triangle_cycle_unsafe C hcycle h3 hsafe
    · exact digraph_safe17_four_cycle_unsafe C hcycle h4 hsafe
