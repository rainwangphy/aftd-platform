import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet

/-!
# can_force

Topic: social_choice   Node: 4d5ecfd027dd

Provenance: formalization of a published result. Source: arXiv:2611.26224 Section 3

A coalition of voters C can force an alternative x under voting rule f if there is a profile P at which the coalitional option set of C is the singleton {x}.
-/

/-- A coalition C can force an alternative x under f if its option set for some report is the singleton {x}. -/
def can_force {N A : Type*} (f : (N → LinearOrder A) → A) (C : Finset N) (x : A) : Prop := ∃ P : N → LinearOrder A, voting_option_set f C P = {x}
