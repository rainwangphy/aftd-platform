import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopRank
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopChoice
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTopChoiceTopRank

/-!
# SocialChoice.Voting.topRank_eq_topChoice

Topic: social_choice   Node: 0ee53884a43f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topRank_eq_topChoice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.topRank_eq_topChoice
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
theorem SocialChoice.Voting.topRank_eq_topChoice [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) (a : A) (ha : TopRank P i a) :
    a = topChoice P i := by
  by_contra hne
  have h₁ := ha (topChoice P i) (Ne.symm hne)
  have h₂ := topChoice_topRank P i a hne
  letI := P.pref i
  exact (lt_asymm h₁ h₂).elim
