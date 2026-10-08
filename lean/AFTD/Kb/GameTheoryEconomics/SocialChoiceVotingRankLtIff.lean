import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRankLtOfLt
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.rank_lt_iff

Topic: social_choice   Node: 3cf2ed9a3d04

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.rank_lt_iff`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.rank_lt_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
theorem SocialChoice.Voting.rank_lt_iff [Fintype A] (r : LinearOrder A) {a b : A} :
    rank r a < rank r b ↔ BallotPrefers r a b := by
  constructor
  · intro h
    letI := r
    by_contra hnot
    have hne : a ≠ b := by
      intro hab
      subst hab
      omega
    have hba : b < a := lt_of_le_of_ne (le_of_not_gt hnot) (Ne.symm hne)
    have hlt := rank_lt_of_lt r (by simpa [BallotPrefers] using hba)
    omega
  · exact rank_lt_of_lt r
