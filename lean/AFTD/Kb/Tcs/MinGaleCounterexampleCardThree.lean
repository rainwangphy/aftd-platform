import AFTD.Prelude
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# min_gale_counterexample_card_three

Topic: combinatorics   Node: 0faa875e7e06

Provenance: formalization of a published result. Source: arXiv:2610.28828, Sec. 5, Question 2

The minimum cardinality `min_gale_counterexample_card_three` of a finite counterexample to Gale's conjecture in dimension 3 is the infimum of the set of natural numbers m such that there exists a finite subset V of `EuclideanSpace ℝ (Fin 3)` with cardinality m satisfying `is_gale_counterexample_three V`.
-/

/-- The minimum cardinality m(3) of a finite counterexample to Gale's conjecture in dimension 3. -/
noncomputable def min_gale_counterexample_card_three : ℕ := sInf { m : ℕ | ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = m ∧ is_gale_counterexample_three V }
