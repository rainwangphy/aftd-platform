import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingAcyclicBallot

/-!
# SocialChoice.Voting.condorcetProfile

Topic: social_choice   Node: 86d27b0f6b0d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.condorcetProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.condorcetProfile
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.condorcetProfile [Fintype N] [Fintype A]
    (S T _U : Set N) (x y z : A)
    (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : Profile N A := by
  classical
  exact
    { pref := fun i =>
        if i ∈ S then
          acyclicBallot A hxy hxz hyz
        else if i ∈ T then
          acyclicBallot A hyz (Ne.symm hxy) (Ne.symm hxz)
        else
          acyclicBallot A (Ne.symm hxz) (Ne.symm hyz) hxy }
