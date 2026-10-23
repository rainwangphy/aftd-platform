import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaStep
import AFTD.Kb.Tcs.TwoWayDfaAccepts
import AFTD.Kb.Tcs.TwoWayDfaRun

/-!
# two_way_dfa_accepts_of_s_eq_f

Topic: automata   Node: a17896e1fec4

Provenance: helper lemma. sanity lemma for two_way_dfa_accepts

Sanity: if the initial state is the final state, every word is accepted (at time 0).
-/

theorem two_way_dfa_accepts_of_s_eq_f {σ Q : Type*} (A : two_way_dfa σ Q) (h : A.s = A.f)
    (w : List σ) : two_way_dfa_accepts A w :=
  ⟨0, by simp [two_way_dfa_run, h]⟩
