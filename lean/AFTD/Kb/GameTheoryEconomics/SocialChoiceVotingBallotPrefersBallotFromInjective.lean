import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT

/-!
# SocialChoice.Voting.BallotPrefers_ballotFromInjective

Topic: social_choice   Node: 2161e9f76b1e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotPrefers_ballotFromInjective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.BallotPrefers_ballotFromInjective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
@[simp]
theorem SocialChoice.Voting.BallotPrefers_ballotFromInjective {B : Type*} (rB : LinearOrder B)
    (f : A → B) (hf : Function.Injective f) (a b : A) :
    BallotPrefers (ballotFromInjective rB f hf) a b ↔
      @LT.lt B (ballotLT rB) (f a) (f b) := by
  rfl
