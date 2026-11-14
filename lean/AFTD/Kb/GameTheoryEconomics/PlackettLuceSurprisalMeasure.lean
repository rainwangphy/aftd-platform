import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropy
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProb
import AFTD.Kb.GameTheoryEconomics.RankingsOf

/-!
# plackett_luce_surprisal_measure

Topic: social_choice   Node: 4d5dad7d62c2

Provenance: formalization of a published result. Source: OP-1712

For weights w : ℕ → ℝ and number of items n : ℕ, the pushforward measure on ℝ of the standardized surprisal (-log P(l) - H) / sqrt(n) under the Plackett-Luce distribution on rankings of Finset.range n, where H is the Plackett-Luce entropy of Finset.range n.
-/

/-- Standardized surprisal distribution for Plackett-Luce rankings of n alternatives. -/
noncomputable def plackett_luce_surprisal_measure (w : ℕ → ℝ) (n : ℕ) : MeasureTheory.Measure ℝ := let H := plackett_luce_entropy w (Finset.range n)
  ∑ l ∈ rankings_of (Finset.range n),
    ENNReal.ofReal (plackett_luce_prob w l) • MeasureTheory.Measure.dirac ((-Real.log (plackett_luce_prob w l) - H) / Real.sqrt (n : ℝ))
