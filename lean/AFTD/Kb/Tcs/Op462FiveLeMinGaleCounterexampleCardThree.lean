import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.IsGaleCounterexampleThree
import AFTD.Kb.Tcs.Op462GaleCounterexampleCardThreeGeFive

/-!
# op_462_five_le_min_gale_counterexample_card_three

Topic: combinatorics   Node: 65a9e5eec21c

Provenance: helper lemma. arXiv:2610.28828 Sec. 5

If there exists a finite counterexample to Gale's conjecture in dimension 3, then the minimum cardinality min_gale_counterexample_card_three of such a counterexample is at least 5.
-/

/-- If a finite counterexample to Gale's conjecture in dimension 3 exists, then min_gale_counterexample_card_three is at least 5. -/
theorem op_462_five_le_min_gale_counterexample_card_three
    (h : ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), is_gale_counterexample_three V) :
    5 ≤ min_gale_counterexample_card_three := by
  unfold min_gale_counterexample_card_three
  obtain ⟨V, hV⟩ := h
  apply le_csInf
  · exact ⟨V.card, V, rfl, hV⟩
  · rintro m ⟨W, rfl, hW⟩
    exact op_462_gale_counterexample_card_three_ge_five W hW
