import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet

/-!
# has_type_w_manipulation

Topic: social_choice   Node: 83d2d750708c

Provenance: formalization of a published result. Source: arXiv:2611.26224 Definition 1 -- Obvious group manipulations in voting

A coalition C has an obvious group manipulation of type (W) at profile P by reporting P_dev under voting rule f if there exists an outcome x in the truthful option set of C such that every outcome y in the deviation option set is strictly preferred to x by every member of C.
-/

/-- A coalition has an obvious group manipulation of type (W) if some outcome in the truthful option set is strictly worse for every coalition member than every outcome in the deviation option set. -/
def has_type_w_manipulation {N A : Type*} (f : (N → LinearOrder A) → A)
    (C : Finset N) (P P_dev : N → LinearOrder A) : Prop :=
  let T := voting_option_set f C P
  let F := voting_option_set f C P_dev
  ∃ x ∈ T, ∀ y ∈ F, ∀ i ∈ C, @LT.lt A (P i).toLT x y
