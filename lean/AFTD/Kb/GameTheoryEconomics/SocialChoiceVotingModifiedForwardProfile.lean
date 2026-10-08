import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.modifiedForwardProfile

Topic: social_choice   Node: 44ffb1d884ad

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.modifiedForwardProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.modifiedForwardProfile
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.modifiedForwardProfile [Fintype N] [Fintype A]
    (P : Profile N A) (C : Set N) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Profile N A := by
  classical
  exact
    { pref := fun i =>
        if i ∈ C then
          betweenBallot (P.pref i) hxy hxz hyz
        else
          topBallot (P.pref i) y }
