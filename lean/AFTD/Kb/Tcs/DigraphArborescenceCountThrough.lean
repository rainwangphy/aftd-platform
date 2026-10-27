import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphArborescenceCountAtThrough

/-!
# digraph_arborescence_count_through

Topic: graphs   Node: a85f91fa8e8c

Provenance: helper lemma. step towards tournament_not_near_regular_exists_improving_tournament

through(D, a → b): the number of spanning arborescences of D, over all choices of root, that use the arc a → b.
-/

/-- Total number of arborescences of D (summed over all roots) that use the arc a → b. -/
def digraph_arborescence_count_through {n : ℕ} (D : Digraph (Fin n)) [DecidableRel D.Adj] (a b : Fin n) : ℕ := ∑ r, digraph_arborescence_count_at_through D r a b
