import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfaRun
import AFTD.Kb.Tcs.TwoWayDfaStep
import AFTD.Kb.Tcs.TwoWayDfa

/-!
# two_way_dfa_run_succ

Topic: automata   Node: 5e0c9ac8b250

Provenance: helper lemma. arXiv:2610.18897

For any two-way deterministic finite automaton A, input word w, and time t, the configuration after t + 1 computation steps is the result of applying one transition step to the configuration at time t.
-/

/-- The configuration of a 2DFA after t + 1 steps is obtained by applying one step to the configuration after t steps. -/
theorem two_way_dfa_run_succ {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (t : ℕ) :
    two_way_dfa_run A w (t + 1) = (two_way_dfa_run A w t).bind (two_way_dfa_step A w) := by
  dsimp [two_way_dfa_run]
  exact Function.iterate_succ_apply' (fun c => c.bind (two_way_dfa_step A w)) t (some (A.s, 0))
