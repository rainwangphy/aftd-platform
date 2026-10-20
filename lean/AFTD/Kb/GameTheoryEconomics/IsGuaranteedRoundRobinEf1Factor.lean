import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.IsAlphaEf1
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation

/-!
# is_guaranteed_round_robin_ef1_factor

Topic: fair_division   Node: 3bd6bd7655de

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

A factor α is guaranteed for n agents under Round-Robin if for every number of goods m, every nonnegative additive valuation profile w, and every pure Nash equilibrium rank under the Round-Robin sequence, the induced allocation is α-EF1.
-/

/-- A factor α is guaranteed for n agents under Round-Robin if every pure Nash equilibrium of every n-agent additive instance induces an α-EF1 allocation. -/
def is_guaranteed_round_robin_ef1_factor (n : ℕ) [NeZero n] (α : ℝ) : Prop :=
  ∀ (m : ℕ) (w : Fin n → Fin m → ℝ),
    (∀ i g, 0 ≤ w i g) →
    ∀ (rank : Fin n → Fin m ≃ Fin m),
      is_picking_sequence_pne
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (round_robin_sequence n m) rank →
      is_alpha_ef1 α
        (SocialChoice.FairDivision.Indivisible.AdditiveValuation.toValuation ⟨w⟩)
        (picking_sequence_outcome (round_robin_sequence n m) rank)
