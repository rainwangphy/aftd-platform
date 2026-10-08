import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenKeyInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank

/-!
# SocialChoice.Voting.betweenBallot_yz

Topic: social_choice   Node: 9152eae2ab58

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.betweenBallot_yz`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.betweenBallot_yz
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.betweenBallot_yz [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    BallotPrefers (betweenBallot r hxy hxz hyz) y z := by
  simp [betweenBallot, betweenKey, Ne.symm hxy, Ne.symm hxz, Ne.symm hyz]
