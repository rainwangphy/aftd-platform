import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne

/-!
# is_guaranteed_sequence_ef1_factor

Topic: fair_division   Node: 58f82cbfda58

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 2 and Sec. 6

A factor α is guaranteed for a picking sequence mechanism seq with n agents if for every nonnegative additive valuation profile and every pure Nash equilibrium reported ranking profile, the outcome of the picking sequence is α-EF1.
-/

/-- A factor α is guaranteed for a picking sequence if at every pure Nash equilibrium under nonnegative additive valuations, the induced allocation is α-EF1. -/
def is_guaranteed_sequence_ef1_factor (n : ℕ) (seq : List (Fin n)) (α : ℝ) : Prop :=
  ∀ (w : Fin n → Fin seq.length → ℝ),
    (∀ i g, 0 ≤ w i g) →
    ∀ (rank : Fin n → Fin seq.length ≃ Fin seq.length),
      is_picking_sequence_pne
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        seq rank →
      is_alpha_ef1 α
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (picking_sequence_outcome seq rank)
