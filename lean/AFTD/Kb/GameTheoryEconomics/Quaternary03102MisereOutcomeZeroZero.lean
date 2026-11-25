import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Quaternary03102MisereOutcome
import AFTD.Kb.GameTheoryEconomics.MisereOutcome

/-!
# quaternary_03102_misere_outcome_zero_zero

Topic: combinatorial_games   Node: ea0dffbfcb58

Provenance: helper lemma. arXiv:2611.29198 Section 2.1

In the quaternary game 0.3102, the empty position (0, 0) has misère outcome N.
-/

/-- The terminal position (0, 0) has misère outcome N in 0.3102. -/
theorem quaternary_03102_misere_outcome_zero_zero : quaternary_03102_misere_outcome 0 0 = MisereOutcome.N := rfl
