import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingScoringWinners
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.scoringRule

Topic: social_choice   Node: 58fabf625549

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.scoringRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Generic positional scoring rule. The first argument is the number of alternatives, and the second is the zero-based rank.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Generic positional scoring rule. The first argument is the number of alternatives, and the second is the zero-based rank. -/
noncomputable def SocialChoice.Voting.scoringRule (score : Nat → Nat → Int)
    [Fintype N] [Fintype A] : VotingRule N A :=
  fun P => scoringWinners P (fun r => score (Fintype.card A) r)
