import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.votersPreferring

Topic: social_choice   Node: 01517f519cc7

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.votersPreferring`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Voters who strictly prefer `a` to `b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Voters who strictly prefer `a` to `b`. -/
noncomputable def SocialChoice.Voting.votersPreferring [Fintype N] [Fintype A]
    (P : Profile N A) (a b : A) : Finset N :=
  Finset.univ.filter (fun i => Prefers P i a b)
