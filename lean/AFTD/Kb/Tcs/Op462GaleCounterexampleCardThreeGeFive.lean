import AFTD.Prelude
import AFTD.Kb.Tcs.IsGaleCounterexampleThree
import AFTD.Kb.Tcs.Op462NotIsGaleCounterexampleThreeOfCardLeFour

/-!
# op_462_gale_counterexample_card_three_ge_five

Topic: combinatorics   Node: 726531a4f4e0

Provenance: helper lemma. arXiv:2610.28828, Sec. 5, Question 2

For every finite subset V of `EuclideanSpace ℝ (Fin 3)`, if V is a counterexample to Gale's conjecture in dimension 3 (`is_gale_counterexample_three V`), then the cardinality of V is at least 5.
-/

/-- Every counterexample to Gale's conjecture in dimension 3 has at least 5 points. -/
theorem op_462_gale_counterexample_card_three_ge_five (V : Finset (EuclideanSpace ℝ (Fin 3))) (hV : is_gale_counterexample_three V) : 5 ≤ V.card := by
  by_contra h
  have h4 : V.card ≤ 4 := by omega
  exact op_462_not_is_gale_counterexample_three_of_card_le_four V h4 hV
