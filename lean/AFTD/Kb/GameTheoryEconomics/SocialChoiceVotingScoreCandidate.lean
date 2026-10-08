import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank

/-!
# SocialChoice.Voting.scoreCandidate

Topic: social_choice   Node: 0adf85a09418

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.scoreCandidate`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Total score for a candidate under a positional score vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Total score for a candidate under a positional score vector. -/
noncomputable def SocialChoice.Voting.scoreCandidate [Fintype N] [Fintype A]
    (P : Profile N A) (score : Nat → Int) (a : A) : Int :=
  ∑ i : N, score (rank (P.pref i) a)
