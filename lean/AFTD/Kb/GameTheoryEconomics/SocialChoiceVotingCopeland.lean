import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingCopelandScore
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingVotingRule
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.copeland

Topic: social_choice   Node: 75a640a9a3a5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.copeland`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Copeland winners.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Copeland winners. -/
noncomputable def SocialChoice.Voting.copeland [Fintype N] [Fintype A] : VotingRule N A := by
  intro P
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int := (Finset.univ.image (fun a => copelandScore P a)).max' (hA.image _)
    exact Finset.univ.filter (fun a => copelandScore P a = maxScore)
  · exact ∅
