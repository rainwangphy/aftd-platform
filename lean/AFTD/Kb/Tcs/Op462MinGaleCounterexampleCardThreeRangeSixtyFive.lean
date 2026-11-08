import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.Op462MinGaleCounterexampleCardThreeInRange
import AFTD.Kb.Tcs.Op462MinCardLeOfIntegerWitness
import AFTD.Kb.Tcs.Op462Coords65
import AFTD.Kb.Tcs.Op462Edges65
import AFTD.Kb.Tcs.Op462Coords65DiameterSquaredLe
import AFTD.Kb.Tcs.Op462Coords65EdgesSquaredGe
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.Op462NoFourColoring65
import AFTD.Kb.Tcs.Op462MinGaleCounterexampleCardThreeLeSixtyFive

/-!
# op_462_min_gale_counterexample_card_three_range_sixty_five

Topic: combinatorics   Node: 4dfafb19c425

Provenance: helper lemma. arXiv:2610.28828 Sec. 5, Question 2

The minimum cardinality `min_gale_counterexample_card_three` of a finite counterexample to Gale's conjecture in dimension 3 satisfies 5 ≤ min_gale_counterexample_card_three and min_gale_counterexample_card_three ≤ 65.
-/

/-- The minimum cardinality of a finite counterexample to Gale's conjecture in dimension 3 lies in the range [5, 65]. -/
theorem op_462_min_gale_counterexample_card_three_range_sixty_five : 5 ≤ min_gale_counterexample_card_three ∧ min_gale_counterexample_card_three ≤ 65 := by
  exact ⟨op_462_min_gale_counterexample_card_three_in_range.1, op_462_min_gale_counterexample_card_three_le_sixty_five⟩
