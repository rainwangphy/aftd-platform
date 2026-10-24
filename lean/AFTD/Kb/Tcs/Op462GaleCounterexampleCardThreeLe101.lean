import AFTD.Prelude
import AFTD.Tactic.NumBounds
import AFTD.Kb.Tcs.IsGaleCounterexampleThree
import AFTD.Kb.Tcs.Op462CounterexampleOfIntegerWitness
import AFTD.Kb.Tcs.Op462CounterexampleExtendCard
import AFTD.Kb.Tcs.Op462Coords65
import AFTD.Kb.Tcs.Op462Edges65
import AFTD.Kb.Tcs.Op462NoFourColoring65
import AFTD.Kb.Tcs.Op462Coords65DiameterSquaredLe
import AFTD.Kb.Tcs.Op462Coords65EdgesSquaredGe
import AFTD.Kb.Tcs.GaleSigmaThree

/-!
# op_462_gale_counterexample_card_three_le_101

Topic: combinatorics   Node: e161b333b612

Provenance: formalization of a published result. Source: arXiv:2610.28828, Theorem 2

There exists a finite subset V of `EuclideanSpace ℝ (Fin 3)` with cardinality 101 that is a counterexample to Gale's conjecture in dimension 3 (`is_gale_counterexample_three V`).
-/

/-- Theorem 2 of arXiv:2610.28828: there exists a 101-point counterexample to Gale's conjecture in dimension 3. -/
theorem op_462_gale_counterexample_card_three_le_101 : ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = 101 ∧ is_gale_counterexample_three V := by
  have hgap : gale_sigma_three^2 <
      ((7887420401648046950672144846523981 : ℤ) : ℝ) / ((10^17 : ℤ) : ℝ)^2 := by
    unfold gale_sigma_three
    rw [Real.sq_sqrt (by positivity)]
    num_ineq
  obtain ⟨V, hcard, hV⟩ := op462_counterexample_of_integer_witness 65 (10^17)
    7887420401648046950672144846523981 (by norm_num)
    op462_coords65 op462_edges65 op462_coords65_diameter_squared_le
    op462_coords65_edges_squared_ge hgap op462_no_four_coloring65 0 1 (by decide)
  exact op462_counterexample_extend_card V hV 101 (by omega)
