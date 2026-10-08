import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsTotal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPlurality
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingScoringRuleIsTotal
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPluralityScore
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.plurality_isTotal

Topic: social_choice   Node: 70db0147d69e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.plurality_isTotal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.plurality_isTotal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
theorem SocialChoice.Voting.plurality_isTotal [Fintype N] [Fintype A] [Nonempty A] :
    IsTotal (N := N) (A := A) plurality :=
  scoringRule_isTotal pluralityScore
