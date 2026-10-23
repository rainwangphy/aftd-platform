import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaStep

/-!
# two_way_dfa_step_right

Topic: automata   Node: 69ddd1f74bcf

Provenance: helper lemma. sanity lemma for two_way_dfa_step

Sanity: on the right endmarker a step applies δR and moves to position |w|.
-/

theorem two_way_dfa_step_right {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (q : Q) :
    two_way_dfa_step A w (q, w.length + 1) = (A.δR q).map (fun q' => (q', w.length)) := by
  simp [two_way_dfa_step]
