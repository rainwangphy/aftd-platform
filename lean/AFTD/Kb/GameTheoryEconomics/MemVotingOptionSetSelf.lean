import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet

/-!
# mem_voting_option_set_self

Topic: social_choice   Node: 3bff5c7687d6

Provenance: helper lemma. folklore

For any voting rule f, coalition of voters C, and preference profile P, the truthful outcome f P belongs to the option set voting_option_set f C P of C at P.
-/

/-- The outcome f P belongs to the option set of any coalition C at profile P. -/
lemma mem_voting_option_set_self {N A : Type*} (f : (N → LinearOrder A) → A)
    (C : Finset N) (P : N → LinearOrder A) :
    f P ∈ voting_option_set f C P := ⟨P, fun _ _ => rfl, rfl⟩
