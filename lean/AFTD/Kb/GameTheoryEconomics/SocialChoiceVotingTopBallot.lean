import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopKeyInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.topBallot

Topic: social_choice   Node: d34b74729614

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topBallot`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topBallot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.topBallot [Fintype A] (r : LinearOrder A) (y : A) :
    LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (topKey r y)
    (topKey_injective r y)
