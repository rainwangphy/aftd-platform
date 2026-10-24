import AFTD.Prelude
import AFTD.Kb.Tcs.IsGaleCounterexampleThree
import AFTD.Kb.Tcs.GaleDistanceGraph
import AFTD.Kb.Tcs.GaleSigmaThree

/-!
# op_462_not_is_gale_counterexample_three_of_card_le_four

Topic: combinatorics   Node: 20882588ee6d

Provenance: helper lemma. arXiv:2610.28828, Sec. 5, Question 2

For every finite subset V of `EuclideanSpace ℝ (Fin 3)`, if the cardinality of V is at most 4, then V is not a counterexample to Gale's conjecture in dimension 3 (that is, `¬ is_gale_counterexample_three V`).
-/

/-- Any subset of R^3 of cardinality at most 4 is not a counterexample to Gale's conjecture. -/
theorem op_462_not_is_gale_counterexample_three_of_card_le_four (V : Finset (EuclideanSpace ℝ (Fin 3))) (hV : V.card ≤ 4) : ¬ is_gale_counterexample_three V := by
  intro h
  obtain ⟨hdiam, hcol⟩ := h
  apply hcol
  have hcard : Fintype.card V ≤ 4 := by rw [Fintype.card_coe]; exact hV
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  refine ⟨SimpleGraph.Coloring.mk (fun v => Fin.castLE hcard (e v)) ?_⟩
  intro v w hadj
  have hne : v ≠ w := hadj.1
  intro hEq
  apply hne
  apply e.injective
  exact Fin.castLE_injective hcard hEq
