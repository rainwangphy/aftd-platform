import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRankLtIff
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopBallot
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKeyInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.topBallot_preserves

Topic: social_choice   Node: 3684831bc4d8

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topBallot_preserves`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topBallot_preserves
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.topBallot_preserves [Fintype A] (r : LinearOrder A) {y a b : A}
    (ha : a ≠ y) (hb : b ≠ y) :
    BallotPrefers (topBallot r y) a b ↔ BallotPrefers r a b := by
  simp [topBallot, topKey, ha, hb, rank_lt_iff]
