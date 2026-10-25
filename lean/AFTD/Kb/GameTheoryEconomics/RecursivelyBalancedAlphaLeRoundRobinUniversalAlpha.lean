import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RecursivelyBalancedAlpha
import AFTD.Kb.GameTheoryEconomics.RoundRobinUniversalAlpha
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceIsRecursivelyBalanced
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.PickingSequenceAlpha
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.IsRecursivelyBalanced
import AFTD.Kb.GameTheoryEconomics.IsRoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedSequenceEf1Factor
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.Tcs.G

/-!
# recursively_balanced_alpha_le_round_robin_universal_alpha

Topic: fair_division   Node: bc27fe386222

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

The universal EF1 approximation factor for recursively balanced sequences recursively_balanced_alpha is at most the universal factor for Round-Robin sequences round_robin_universal_alpha.
-/

lemma recursively_balanced_alpha_le_round_robin_universal_alpha_zero_is_guaranteed
    (n : ℕ) (seq : List (Fin n)) :
    is_guaranteed_sequence_ef1_factor n seq 0 := by
  intro w hw rank hpne i j hij hAj
  rcases hAj with ⟨g, hg⟩
  refine ⟨g, hg, ?_⟩
  dsimp [SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation]
  rw [zero_mul]
  exact Finset.sum_nonneg fun x _ => hw i x

lemma recursively_balanced_alpha_le_round_robin_universal_alpha_zero_le_alpha
    (n : ℕ) (seq : List (Fin n)) :
    0 ≤ picking_sequence_alpha n seq := by
  dsimp [picking_sequence_alpha]
  by_cases h : BddAbove {α | is_guaranteed_sequence_ef1_factor n seq α}
  · exact le_csSup h (recursively_balanced_alpha_le_round_robin_universal_alpha_zero_is_guaranteed n seq)
  · have h0 : sSup {α | is_guaranteed_sequence_ef1_factor n seq α} = 0 := by
      rw [Real.sSup_def]
      split_ifs with h'
      · exact False.elim (h h'.2)
      · rfl
    rw [h0]

/-- The universal EF1 approximation factor for recursively balanced sequences is at most that of Round-Robin. -/
theorem recursively_balanced_alpha_le_round_robin_universal_alpha :
    recursively_balanced_alpha ≤ round_robin_universal_alpha := by
  dsimp [recursively_balanced_alpha, round_robin_universal_alpha]
  apply csInf_le_csInf
  · use 0
    rintro x ⟨n, seq, hseq, hn, rfl⟩
    exact recursively_balanced_alpha_le_round_robin_universal_alpha_zero_le_alpha n seq
  · use picking_sequence_alpha 2 (round_robin_sequence 2 0)
    refine ⟨2, round_robin_sequence 2 0, ⟨inferInstance, rfl⟩, le_rfl, rfl⟩
  · rintro y ⟨n, seq, ⟨inst, heq⟩, hn, rfl⟩
    refine ⟨n, seq, ?_, hn, rfl⟩
    rw [heq]
    exact round_robin_sequence_is_recursively_balanced n seq.length
