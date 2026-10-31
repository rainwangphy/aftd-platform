import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAtReverseArcAddThrough
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough
import AFTD.Kb.Tcs.DigraphArborescenceCount
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphReverseArc
import AFTD.Kb.Tcs.DigraphArborescenceCountThrough
import AFTD.Kb.Tcs.DigraphArborescenceCountAt

/-!
# digraph_arborescence_count_reverse_arc_add_through

Topic: graphs   Node: 54af597d8092

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

Reversing a single arc u → v of a tournament satisfies tau(T) + through(T', v → u) = tau(T') + through(T, u → v), so the gain in the two-sided arborescence count is exactly the excess of the new through-count over the old one.
-/

/-- Summed form of the reversal identity: tau(T) + through(T', v → u) = tau(T') + through(T, u → v). -/
theorem digraph_arborescence_count_reverse_arc_add_through {n : ℕ} (T : Digraph (Fin n))
    [DecidableRel T.Adj] (hT : digraph_is_tournament T) (u v : Fin n) (huv : T.Adj u v) :
    digraph_arborescence_count T + digraph_arborescence_count_through (digraph_reverse_arc T u v) v u =
      digraph_arborescence_count (digraph_reverse_arc T u v) + digraph_arborescence_count_through T u v := by
  simp only [digraph_arborescence_count, digraph_arborescence_count_through]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl
    (fun r _ => digraph_arborescence_count_at_reverse_arc_add_through T hT u v huv r)
