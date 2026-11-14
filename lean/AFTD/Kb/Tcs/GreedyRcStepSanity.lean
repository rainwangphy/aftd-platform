import AFTD.Prelude
import AFTD.Kb.Tcs.GreedyRcStep
import AFTD.Kb.Tcs.StringOverlapLen
import AFTD.Kb.Tcs.RevComp
import AFTD.Kb.Tcs.StringOverlapMerge

/-!
# greedy_rc_step_sanity

Topic: approximation   Node: 27835e714012

Provenance: helper lemma. Sanity check of greedy_rc_step (arXiv:2611.16573)

With cm = id, one GREEDY-RC step on {12, 23} gives {123}.
-/

theorem greedy_rc_step_sanity :
    greedy_rc_step id ({[1, 2], [2, 3]} : Finset (List ℕ)) {[1, 2, 3]} := by
  unfold greedy_rc_step; decide
