import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingScoringRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPluralityScore
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.plurality

Topic: social_choice   Node: 2a604485740d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.plurality`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Plurality rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Plurality rule. -/
noncomputable def SocialChoice.Voting.plurality [Fintype N] [Fintype A] : VotingRule N A :=
  scoringRule pluralityScore
