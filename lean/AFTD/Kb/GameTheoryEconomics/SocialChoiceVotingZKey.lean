import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.zKey

Topic: social_choice   Node: 960ed1cd2593

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.zKey`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/ProfileSurgery.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The rank function used by `zBallot`: first separate alternatives by membership in `R`, then use the relevant source ballot's rank.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- The rank function used by `zBallot`: first separate alternatives by membership in `R`, then use the relevant source ballot's rank. -/
noncomputable def SocialChoice.Voting.zKey [Fintype A] (P Q : LinearOrder A) (R : Set A)
    [∀ a : A, Decidable (a ∈ R)] (a : A) : Nat :=
  let base := Fintype.card A + 1
  let block := if a ∈ R then 0 else 1
  let localRank := if a ∈ R then rank P a else rank Q a
  block * base + localRank
