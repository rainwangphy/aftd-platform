import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsOmg
import AFTD.Kb.GameTheoryEconomics.HasTypeWManipulation
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet
import AFTD.Kb.GameTheoryEconomics.HasObviousGroupManipulation

/-!
# is_omg_of_has_type_w_manipulation

Topic: social_choice   Node: b887999bef33

Provenance: helper lemma. arXiv:2611.26224

If there exist a nonempty coalition C and preference profiles P, P_dev such that C has an obvious group manipulation of type (W) at P by reporting P_dev under voting rule f, then f is obviously manipulable by groups (OMG).
-/

/-- An obvious group manipulation of type (W) implies that the voting rule is obviously manipulable by groups (OMG). -/
lemma is_omg_of_has_type_w_manipulation {N A : Type*} (f : (N → LinearOrder A) → A)
    (h : ∃ (C : Finset N), C.Nonempty ∧ ∃ (P P_dev : N → LinearOrder A),
      has_type_w_manipulation f C P P_dev) :
    is_omg f := by
  rcases h with ⟨C, hC, P, P_dev, hw⟩
  exact ⟨C, hC, P, P_dev, Or.inl hw⟩
