import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MisereOutcome
import AFTD.Kb.GameTheoryEconomics.Quaternary03102Options

/-!
# quaternary_03102_misere_outcome_comp

Topic: combinatorial_games   Node: af0313a66bb2

Provenance: formalization of a published result. Source: arXiv:2611.29198 Section 2.1

For fuel, x, y : ℕ, the fuel-bounded misère outcome quaternary_03102_misere_outcome_comp fuel x y of a two-heap position (x, y) in the quaternary game 0.3102 returns MisereOutcome.N when fuel = 0; and for fuel = fuel' + 1, it returns MisereOutcome.N if x = 0 and y = 0, else returns MisereOutcome.N if there exists p ∈ quaternary_03102_options x y such that quaternary_03102_misere_outcome_comp fuel' p.1 p.2 = MisereOutcome.P, and MisereOutcome.P otherwise.
-/

/-- Fuel-bounded misère outcome computation for two heaps in 0.3102. -/
def quaternary_03102_misere_outcome_comp : ℕ → ℕ → ℕ → MisereOutcome
| 0, _, _ => MisereOutcome.N
| fuel + 1, x, y =>
  if x = 0 ∧ y = 0 then MisereOutcome.N
  else if ∃ p ∈ quaternary_03102_options x y,
    quaternary_03102_misere_outcome_comp fuel p.1 p.2 = MisereOutcome.P then
    MisereOutcome.N
  else
    MisereOutcome.P
