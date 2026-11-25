import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Quaternary03102HeapOptions

/-!
# quaternary_03102_heap_options_zero

Topic: combinatorial_games   Node: 1976b4ded83b

Provenance: helper lemma. arXiv:2611.29198 Section 2.4

In the quaternary game 0.3102, a heap of size 0 has no legal options.
-/

/-- A heap of size 0 has no legal moves in 0.3102. -/
theorem quaternary_03102_heap_options_zero : quaternary_03102_heap_options 0 = ∅ := by
  rfl
