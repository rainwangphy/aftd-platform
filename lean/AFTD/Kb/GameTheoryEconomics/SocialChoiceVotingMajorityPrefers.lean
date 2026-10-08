import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingMarginPos

/-!
# SocialChoice.Voting.MajorityPrefers

Topic: social_choice   Node: 024c6e36c010

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.MajorityPrefers`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pairwise majority comparison.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Pairwise majority comparison. -/
def SocialChoice.Voting.MajorityPrefers [Fintype N] [Fintype A] (P : Profile N A) (a b : A) : Prop :=
  margin_pos P a b
