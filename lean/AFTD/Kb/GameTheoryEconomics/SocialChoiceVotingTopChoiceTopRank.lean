import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopRank
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopChoice

/-!
# SocialChoice.Voting.topChoice_topRank

Topic: social_choice   Node: f8f29c6c01e0

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topChoice_topRank`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topChoice_topRank
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
theorem SocialChoice.Voting.topChoice_topRank [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) : TopRank P i (topChoice P i) := by
  classical
  intro b hb
  unfold topChoice Prefers
  letI := P.pref i
  exact lt_of_le_of_ne (Finset.min'_le Finset.univ b (by simp)) (Ne.symm hb)
