import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEventualPeriodNat

/-!
# least_eventual_period_nat

Topic: combinatorial_games   Node: 5fa40925e83b

Provenance: formalization of a published result. Source: arXiv:2611.31336

The least eventual period of a sequence g : ℕ → ℕ of natural numbers is the infimum of the set of its positive eventual periods.
-/

/-- The least eventual period of a sequence of natural numbers. -/
noncomputable def least_eventual_period_nat (g : ℕ → ℕ) : ℕ := sInf {p : ℕ | is_eventual_period_nat g p}
