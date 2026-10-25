import AFTD.Prelude
import AFTD.Kb.Tcs.CycleWithTwoChords

/-!
# cycle_graph_le_cycle_with_two_chords

Topic: graphs   Node: dbb3969cf43c

Provenance: helper lemma. arXiv:2610.17884 Lemma 4.1

The cycle graph on m vertices is a subgraph of the cycle graph on m vertices with two chords added.
-/

/-- The m-cycle embeds into the cycle with two chords. -/
theorem cycle_graph_le_cycle_with_two_chords (m a : ℕ) :
    SimpleGraph.cycleGraph m ≤ cycle_with_two_chords m a := by
  exact le_sup_left
