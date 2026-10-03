import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProb
import AFTD.Kb.GameTheoryEconomics.RankingsOf

/-!
# plackett_luce_entropy

Topic: social_choice   Node: f6da5ac57a17

Shannon entropy (natural logarithm) of the Plackett-Luce distribution over the rankings of S.
-/

/-- Shannon entropy (natural log) of the Plackett–Luce distribution on rankings of `S`. -/
noncomputable def plackett_luce_entropy (w : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  ∑ l ∈ rankings_of S, Real.negMulLog (plackett_luce_prob w l)
