import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.Prefers

Topic: social_choice   Node: 30f11089bea9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Prefers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Voter `i` strictly prefers `a` to `b` in profile `P`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Voter `i` strictly prefers `a` to `b` in profile `P`. -/
def SocialChoice.Voting.Prefers [Fintype N] [Fintype A] (P : Profile N A) (i : N) (a b : A) : Prop :=
  BallotPrefers (P.pref i) a b
