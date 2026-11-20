import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HasObviousGroupManipulation

/-!
# is_omg

Topic: social_choice   Node: a22251ab2afc

Provenance: formalization of a published result. Source: arXiv:2611.26224 Definition 1

A voting rule f : (N → LinearOrder A) → A is obviously manipulable by groups (OMG) if there exists a nonempty coalition of voters C and preference profiles P, P_dev such that C has an obvious group manipulation at P by reporting P_dev.
-/

/-- A voting rule f is obviously manipulable by groups (OMG) if some nonempty coalition of voters has an obvious group manipulation. -/
def is_omg {N A : Type*} (f : (N → LinearOrder A) → A) : Prop := ∃ (C : Finset N), C.Nonempty ∧ ∃ (P P_dev : N → LinearOrder A), has_obvious_group_manipulation f C P P_dev
