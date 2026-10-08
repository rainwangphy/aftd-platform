import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# SocialChoice.Voting.prefers_trans

Topic: social_choice   Node: b049de57bc4f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.prefers_trans`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.prefers_trans
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.prefers_trans [Fintype N] [Fintype A] (P : Profile N A) (i : N)
    {a b c : A} (hab : Prefers P i a b) (hbc : Prefers P i b c) :
    Prefers P i a c := by
  unfold Prefers BallotPrefers at *
  letI := P.pref i
  exact lt_trans hab hbc
