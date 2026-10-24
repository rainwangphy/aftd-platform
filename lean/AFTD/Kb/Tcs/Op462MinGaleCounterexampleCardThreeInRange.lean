import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.Op462GaleCounterexampleCardThreeGeFive
import AFTD.Kb.Tcs.Op462GaleCounterexampleCardThreeLe101
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# op_462_min_gale_counterexample_card_three_in_range

Topic: combinatorics   Node: d2d49f7f477e

Provenance: helper lemma. arXiv:2610.28828, Sec. 5, Question 2

The minimum cardinality `min_gale_counterexample_card_three` of a finite counterexample to Gale's conjecture in dimension 3 satisfies 5 ≤ min_gale_counterexample_card_three and min_gale_counterexample_card_three ≤ 101.
-/

/-- The minimum cardinality of a counterexample to Gale's conjecture in dimension 3 lies between 5 and 101. -/
theorem op_462_min_gale_counterexample_card_three_in_range : 5 ≤ min_gale_counterexample_card_three ∧ min_gale_counterexample_card_three ≤ 101 := by
  constructor
  · have hne : ({m : ℕ | ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = m ∧ is_gale_counterexample_three V}).Nonempty := by
      obtain ⟨V, hcard, hV⟩ := op_462_gale_counterexample_card_three_le_101
      exact ⟨101, V, hcard, hV⟩
    have hmem := Nat.sInf_mem hne
    obtain ⟨V, hcard, hV⟩ := hmem
    have h5 := op_462_gale_counterexample_card_three_ge_five V hV
    unfold min_gale_counterexample_card_three
    omega
  · obtain ⟨V, hcard, hV⟩ := op_462_gale_counterexample_card_three_le_101
    unfold min_gale_counterexample_card_three
    exact Nat.sInf_le ⟨V, hcard, hV⟩
