import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountReverseArcAddThrough
import AFTD.Kb.Tcs.DigraphArborescenceCountThrough
import AFTD.Kb.Tcs.DigraphArborescenceCount
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphReverseArc

/-!
# tournament_reverse_arc_through_lt_iff_arborescence_lt

Topic: graphs   Node: 55aae36e9d29

Provenance: helper lemma. step towards tournament_reverse_arc_through_count_lt

In a tournament T with an arc u → v, the total through-count strictly increases upon reversing u → v if and only if the total number of spanning arborescences strictly increases.
-/

/-- In a tournament T with arc u → v, the through-count inequality through(T, u → v) < through(reverse(T, u, v), v → u) is equivalent to the total arborescence count inequality tau(T) < tau(reverse(T, u, v)). -/
theorem tournament_reverse_arc_through_lt_iff_arborescence_lt {n : ℕ} (T : Digraph (Fin n))
    [DecidableRel T.Adj] (hT : digraph_is_tournament T) (u v : Fin n) (huv : T.Adj u v) :
    digraph_arborescence_count_through T u v <
      digraph_arborescence_count_through (digraph_reverse_arc T u v) v u ↔
    digraph_arborescence_count T <
      digraph_arborescence_count (digraph_reverse_arc T u v) := by
  have h := digraph_arborescence_count_reverse_arc_add_through T hT u v huv
  constructor <;> intro hlt <;> omega
