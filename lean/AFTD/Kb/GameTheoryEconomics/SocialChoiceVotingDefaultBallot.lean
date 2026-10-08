import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.defaultBallot

Topic: social_choice   Node: b45b18b90204

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.defaultBallot`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.defaultBallot
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.defaultBallot (A : Type*) [Fintype A] : LinearOrder A :=
  ballotFromInjective (inferInstance : LinearOrder (Fin (Fintype.card A)))
    (Fintype.equivFin A) (Fintype.equivFin A).injective
