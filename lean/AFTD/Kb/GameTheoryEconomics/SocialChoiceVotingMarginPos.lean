import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMargin
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.margin_pos

Topic: social_choice   Node: a8e784964d11

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.margin_pos`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Positive pairwise majority margin.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Positive pairwise majority margin. -/
def SocialChoice.Voting.margin_pos [Fintype N] [Fintype A] (P : Profile N A) (a b : A) : Prop :=
  0 < margin P a b
