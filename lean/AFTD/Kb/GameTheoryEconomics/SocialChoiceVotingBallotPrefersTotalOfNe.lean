import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.BallotPrefers.total_of_ne

Topic: social_choice   Node: 6895b99a7ce7

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotPrefers.total_of_ne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.BallotPrefers.total_of_ne
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
theorem SocialChoice.Voting.BallotPrefers.total_of_ne (r : LinearOrder A) {a b : A} (hne : a ≠ b) :
    BallotPrefers r a b ∨ BallotPrefers r b a := by
  letI := r
  rcases lt_or_gt_of_ne hne with hab | hba
  · left
    simpa [BallotPrefers, ballotLT] using hab
  · right
    simpa [BallotPrefers, ballotLT] using hba
