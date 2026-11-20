import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet

/-!
# has_obvious_group_manipulation

Topic: social_choice   Node: db6e6ba1de85

Provenance: formalization of a published result. Source: arXiv:2611.26224 Def. 1, p. 5

A coalition C : Finset N has an obvious group manipulation at profile P : N → LinearOrder A by misreporting P_dev : N → LinearOrder A under voting rule f : (N → LinearOrder A) → A if either condition (W) holds (there exists x in the truthful option set such that every y in the misreport option set satisfies x < y for all i in C) or condition (B) holds (there exists y in the misreport option set such that for every x in the truthful option set, x < y for all i in C).
-/

/-- Obvious group manipulation for coalition C at profile P by misreporting P_dev. -/
def has_obvious_group_manipulation {N A : Type*} (f : (N → LinearOrder A) → A)
    (C : Finset N) (P P_dev : N → LinearOrder A) : Prop :=
  let T := voting_option_set f C P
  let F := voting_option_set f C P_dev
  (∃ x ∈ T, ∀ y ∈ F, ∀ i ∈ C, @LT.lt A (P i).toLT x y) ∨
  (∃ y ∈ F, ∀ x ∈ T, ∀ i ∈ C, @LT.lt A (P i).toLT x y)
