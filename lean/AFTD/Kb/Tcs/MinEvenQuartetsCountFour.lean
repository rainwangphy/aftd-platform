import AFTD.Prelude
import AFTD.Kb.Tcs.MinEvenQuartetsCount

/-!
# min_even_quartets_count_four

Topic: combinatorics   Node: 69ae756d7675

Provenance: helper lemma. scout/2611-32833-even-quartets-and-the-maximum-density-of-a-simplical-3-cocy.md:110

The minimum number of even quartets on 4 vertices is 0.
-/

/-- On 4 vertices, the minimum number of even quartets is 0. -/
theorem min_even_quartets_count_four : min_even_quartets_count 4 = 0 := rfl
