import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersTotalOfNe
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRankLtOfLt
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.rank_injective

Topic: social_choice   Node: f5da8af2bf60

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.rank_injective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.rank_injective
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
theorem SocialChoice.Voting.rank_injective [Fintype A] (r : LinearOrder A) :
    Function.Injective (rank r) := by
  intro a b h
  by_contra hne
  rcases BallotPrefers.total_of_ne r hne with hab | hba
  · have hlt := rank_lt_of_lt r hab
    omega
  · have hlt := rank_lt_of_lt r hba
    omega
