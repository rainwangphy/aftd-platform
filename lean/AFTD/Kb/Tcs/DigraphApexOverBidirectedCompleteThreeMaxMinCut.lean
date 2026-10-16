import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphApexOverBidirectedComplete
import AFTD.Kb.Tcs.DigraphCutCount
import AFTD.Kb.Tcs.DigraphEdgeCount

/-!
# digraph_apex_over_bidirected_complete_three_max_min_cut

Topic: graphs   Node: 9981696c51cb

Provenance: helper lemma. Lemma for digraph_min_cut_additive_bound_fails_for_every_d; arXiv:2610.21381 (Optimally large cuts in both directions), Sec. 6.

For d = 3 (m = 16 arcs), every bipartition of D_3 has a directed cut of size at most 4 = ⌈2m/10⌉, so the bound of Conjecture 6.1 of arXiv:2610.21381 is attained at m = 16.
-/

theorem digraph_apex_over_bidirected_complete_three_max_min_cut
    [DecidableRel (digraph_apex_over_bidirected_complete 3).Adj] :
    (∀ A : Finset (Fin 5), min (digraph_cut_count (digraph_apex_over_bidirected_complete 3) A Aᶜ)
        (digraph_cut_count (digraph_apex_over_bidirected_complete 3) Aᶜ A) ≤ 4) ∧
      digraph_edge_count (digraph_apex_over_bidirected_complete 3) = 16 := by
  have e : ‹DecidableRel (digraph_apex_over_bidirected_complete 3).Adj› =
      fun u v => (inferInstance : Decidable (u ≠ v ∧ v ≠ Fin.last 4)) := Subsingleton.elim _ _
  subst e
  unfold digraph_cut_count digraph_edge_count
  decide
