import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKeyInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank

/-!
# SocialChoice.Voting.topBallot_top

Topic: social_choice   Node: 2cb807244803

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topBallot_top`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topBallot_top
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.topBallot_top [Fintype A] (r : LinearOrder A) {y a : A}
    (h : a ≠ y) : BallotPrefers (topBallot r y) y a := by
  simp [topBallot, topKey, h]
