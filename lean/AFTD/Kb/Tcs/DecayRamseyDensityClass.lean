import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# decay_ramsey_density_class

Topic: combinatorics   Node: efaab2eb9064

Provenance: formalization of a published result. Source: arXiv:2610.20577, Section 1

A sequence a : ℕ+ → ℝ belongs to the class decay_ramsey_density_class if every term a i > 0, a is antitone, and the sum in ℝ≥0∞ satisfies 1 < ∑' i : ℕ+, ENNReal.ofReal (a i).
-/

/-- The class A of positive non-increasing sequences of real numbers with infinite sum strictly greater than 1. -/
def decay_ramsey_density_class (a : ℕ+ → ℝ) : Prop := (∀ i, 0 < a i) ∧ Antitone a ∧ 1 < ∑' i : ℕ+, ENNReal.ofReal (a i)
