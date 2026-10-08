import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenKey
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBetweenKeyInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.betweenBallot

Topic: social_choice   Node: ef70bd99275a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.betweenBallot`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.betweenBallot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.betweenBallot [Fintype A] (r : LinearOrder A)
    {x y z : A} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder Nat) (betweenKey r x y z)
    (betweenKey_injective r hxy hxz hyz)
