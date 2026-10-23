import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaRun
import AFTD.Kb.Tcs.TwoWayDfaStep
import AFTD.Kb.Tcs.TwoWayDfaHalting

/-!
# two_way_dfa_halting_empty

Topic: automata   Node: 587702bd6e9b

Provenance: helper lemma. sanity lemma for two_way_dfa_halting

Sanity: a two-state automaton with no transitions and s ≠ f halts on every input.
-/

theorem two_way_dfa_halting_empty {σ : Type*} :
    two_way_dfa_halting (⟨fun _ _ => none, fun _ => none, fun _ => none, 0, 1⟩ : two_way_dfa σ (Fin 2)) := by
  intro w
  exact ⟨1, Or.inl (by simp [two_way_dfa_run, two_way_dfa_step])⟩
