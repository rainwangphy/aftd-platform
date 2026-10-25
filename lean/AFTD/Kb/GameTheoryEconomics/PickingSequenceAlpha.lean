import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsGuaranteedSequenceEf1Factor

/-!
# picking_sequence_alpha

Topic: fair_division   Node: c2e23274effd

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 6

The best EF1 approximation factor guaranteed for a picking sequence mechanism seq with n agents is the supremum of factors α that are guaranteed for seq.
-/

/-- The best guaranteed EF1 approximation factor for a picking sequence seq with n agents is the supremum of factors α guaranteed for seq. -/
noncomputable def picking_sequence_alpha (n : ℕ) (seq : List (Fin n)) : ℝ :=
  sSup {α : ℝ | is_guaranteed_sequence_ef1_factor n seq α}
