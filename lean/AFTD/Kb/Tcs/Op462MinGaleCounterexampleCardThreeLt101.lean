import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.Op462Lt101OfIntegerWitness
import AFTD.Kb.Tcs.Op462Edges65
import AFTD.Kb.Tcs.Op462Coords65
import AFTD.Kb.Tcs.Op462NoFourColoring65
import AFTD.Kb.Tcs.Op462Coords65DiameterSquaredLe
import AFTD.Kb.Tcs.Op462Coords65EdgesSquaredGe
import AFTD.Kb.Tcs.GaleSigmaThree

/-!
# op_462_min_gale_counterexample_card_three_lt_101

Topic: combinatorics   Node: 71ebda41c952

Provenance: formalization of a published result. Source: Known consequence of the 65-point configuration in https://github.com/vsvor/Gale-conjecture/tree/bd6dc9594c589791f599a0bf4685841bcb5b4486/best_known/3d_65p_088808 accompanying arXiv:2610.28828. Exact-integer geometry and independent non-4-colorability were checked in experiment 4045. This is an upper-bound partial result for Question 2, not the exact minimum.

Open Problem OP-462: the minimum cardinality `min_gale_counterexample_card_three` of a finite counterexample to Gale's conjecture in dimension 3 is strictly less than 101.
-/

open scoped BigOperators

/-- Open problem OP-462: the minimum cardinality of a counterexample to Gale's conjecture in dimension 3 is strictly less than 101. -/
theorem op_462_min_gale_counterexample_card_three_lt_101 : min_gale_counterexample_card_three < 101 := by
  apply op462_lt101_of_integer_witness 65 (by decide) (10^17)
    7887420401648046950672144846523981 (by norm_num)
    op462_coords65 op462_edges65 op462_coords65_diameter_squared_le
    op462_coords65_edges_squared_ge ?_ op462_no_four_coloring65 0 1 (by decide)
  unfold gale_sigma_three
  rw [Real.sq_sqrt (by positivity)]
  num_ineq
