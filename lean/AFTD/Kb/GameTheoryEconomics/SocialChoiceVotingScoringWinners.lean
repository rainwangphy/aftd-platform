import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingScoreCandidate
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.scoringWinners

Topic: social_choice   Node: 93893b15126c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.scoringWinners`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Winners with maximal score.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Winners with maximal score. -/
noncomputable def SocialChoice.Voting.scoringWinners [Fintype N] [Fintype A]
    (P : Profile N A) (score : Nat → Int) : Finset A := by
  classical
  by_cases hA : (Finset.univ : Finset A).Nonempty
  · let maxScore : Int :=
      (Finset.univ.image (fun a => scoreCandidate P score a)).max' (hA.image _)
    exact Finset.univ.filter (fun a => scoreCandidate P score a = maxScore)
  · exact ∅
