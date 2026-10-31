import AFTD.Prelude
import AFTD.Kb.Tcs.MinimalAdvantage

/-!
# minimal_advantage_eleven

Topic: combinatorics   Node: 7a71d0006ff7

Provenance: helper lemma. arXiv:2610.40321 Sec 3

The minimal winning advantage threshold for 11-sided dice is 61.
-/

/-- For n = 11, the minimal winning advantage is 61. -/
theorem minimal_advantage_eleven : minimal_advantage 11 = 61 := by
  norm_num [minimal_advantage]
