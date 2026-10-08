import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingDefaultBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.acyclicBallot

Topic: social_choice   Node: bbfd1dfe2d8d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.acyclicBallot`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.acyclicBallot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.acyclicBallot (A : Type*) [Fintype A]
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) : LinearOrder A :=
  betweenBallot (defaultBallot A) hxy hxz hyz
