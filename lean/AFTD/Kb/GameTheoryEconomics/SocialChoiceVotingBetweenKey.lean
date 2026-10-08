import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.betweenKey

Topic: social_choice   Node: b8fbc707ba37

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.betweenKey`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.betweenKey
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.betweenKey [Fintype A] (r : LinearOrder A)
    (x y z a : A) : Nat :=
  if a = x then 0 else if a = y then 1 else if a = z then 2 else rank r a + 3
