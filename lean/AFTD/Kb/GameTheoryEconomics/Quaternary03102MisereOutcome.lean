import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Quaternary03102MisereOutcomeComp
import AFTD.Kb.GameTheoryEconomics.MisereOutcome

/-!
# quaternary_03102_misere_outcome

Topic: combinatorial_games   Node: aae44f2b7d61

Provenance: formalization of a published result. Source: arXiv:2611.29198 Section 3.1

The misère outcome of a two-heap position (x, y) in the quaternary game 0.3102, defined as quaternary_03102_misere_outcome_comp (x + y) x y.
-/

/-- The two-heap misère outcome function in 0.3102. -/
def quaternary_03102_misere_outcome (x y : ℕ) : MisereOutcome := quaternary_03102_misere_outcome_comp (x + y) x y
