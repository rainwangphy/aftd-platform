import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaStep

/-!
# two_way_dfa_step_left

Topic: automata   Node: ffeee28c999e

Provenance: helper lemma. sanity lemma for two_way_dfa_step

Sanity: on the left endmarker a step applies δL and moves to position 1.
-/

theorem two_way_dfa_step_left {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (q : Q) :
    two_way_dfa_step A w (q, 0) = (A.δL q).map (fun q' => (q', 1)) := by
  simp [two_way_dfa_step]
