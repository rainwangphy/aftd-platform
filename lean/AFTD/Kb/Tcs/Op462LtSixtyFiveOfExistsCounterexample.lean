import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# op462_lt_sixty_five_of_exists_counterexample

Topic: combinatorics   Node: 19ceb48fbaf0

Provenance: helper lemma. step towards op_462_min_gale_counterexample_card_three_lt_sixty_five

If there exists a finite counterexample to Gale's conjecture in dimension 3 with cardinality strictly less than 65, then min_gale_counterexample_card_three < 65.
-/

/-- If there exists a finite counterexample to Gale's conjecture in dimension 3 with cardinality strictly less than 65, then min_gale_counterexample_card_three < 65. -/
theorem op462_lt_sixty_five_of_exists_counterexample (h : ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card < 65 ∧ is_gale_counterexample_three V) : min_gale_counterexample_card_three < 65 := by
  obtain ⟨V, hcard, hV⟩ := h
  have hle : min_gale_counterexample_card_three ≤ V.card := by
    unfold min_gale_counterexample_card_three
    apply Nat.sInf_le
    exact ⟨V, rfl, hV⟩
  exact hle.trans_lt hcard
