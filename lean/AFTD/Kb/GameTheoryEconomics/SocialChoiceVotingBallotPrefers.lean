import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT

/-!
# SocialChoice.Voting.BallotPrefers

Topic: social_choice   Node: 171c538579dd

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotPrefers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ballot `r` ranks `a` strictly above `b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Ballot `r` ranks `a` strictly above `b`. -/
def SocialChoice.Voting.BallotPrefers (r : LinearOrder A) (a b : A) : Prop := by
  exact @LT.lt A (ballotLT r) a b
