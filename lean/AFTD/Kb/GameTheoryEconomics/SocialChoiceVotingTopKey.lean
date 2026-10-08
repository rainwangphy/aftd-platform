import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.topKey

Topic: social_choice   Node: d13e65c5d0bd

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topKey`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topKey
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
noncomputable def SocialChoice.Voting.topKey [Fintype A] (r : LinearOrder A) (y a : A) : Nat :=
  if a = y then 0 else rank r a + 1
