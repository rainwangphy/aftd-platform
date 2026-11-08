import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.Op462MinCardLeOfIntegerWitness
import AFTD.Kb.Tcs.Op462Coords65
import AFTD.Kb.Tcs.Op462Edges65
import AFTD.Kb.Tcs.Op462Coords65DiameterSquaredLe
import AFTD.Kb.Tcs.Op462Coords65EdgesSquaredGe
import AFTD.Kb.Tcs.GaleSigmaThree
import AFTD.Kb.Tcs.Op462NoFourColoring65

/-!
# op_462_min_gale_counterexample_card_three_le_sixty_five

Topic: combinatorics   Node: c3dfff20bf6e

Provenance: helper lemma. arXiv:2610.28828 Sec. 5, Question 2

The minimum cardinality `min_gale_counterexample_card_three` of a finite counterexample to Gale's conjecture in dimension 3 is at most 65.
-/

/-- The minimum cardinality of a finite counterexample to Gale's conjecture in dimension 3 is at most 65. -/
theorem op_462_min_gale_counterexample_card_three_le_sixty_five : min_gale_counterexample_card_three ≤ 65 := by
  apply op_462_min_card_le_of_integer_witness 65 (10^17)
    7887420401648046950672144846523981 (by norm_num)
    op462_coords65 op462_edges65 op462_coords65_diameter_squared_le
    op462_coords65_edges_squared_ge ?_ op462_no_four_coloring65 0 1 (by decide)
  unfold gale_sigma_three
  rw [Real.sq_sqrt (by positivity)]
  num_ineq
