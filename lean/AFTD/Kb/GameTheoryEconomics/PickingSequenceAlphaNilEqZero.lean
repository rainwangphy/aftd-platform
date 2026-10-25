import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceAlpha
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedSequenceEf1Factor
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuationToValuation
import AFTD.Kb.GameTheoryEconomics.IsPickingSequencePne
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAdditiveValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation

/-!
# picking_sequence_alpha_nil_eq_zero

Topic: fair_division   Node: 6913e2e5aab5

Provenance: helper lemma. Degenerate case of picking_sequence_alpha (OP-345, arXiv:2610.23686 Sec. 6): with no items every alpha is guaranteed, so the sSup is over all of R and takes Lean's junk value 0.

For the empty picking sequence every EF1 factor alpha is guaranteed (all bundles are empty), so picking_sequence_alpha, defined as a real sSup, takes the junk value 0.
-/

theorem picking_sequence_alpha_nil_eq_zero (n : ℕ) :
    picking_sequence_alpha n ([] : List (Fin n)) = 0 := by
  have h : {α : ℝ | is_guaranteed_sequence_ef1_factor n ([] : List (Fin n)) α} = Set.univ := by
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
    intro w _ rank _ i j _ hj
    exfalso
    obtain ⟨g, _⟩ := hj
    exact Fin.elim0 ((rank j).symm g)
  unfold picking_sequence_alpha
  rw [h, Real.sSup_univ]
