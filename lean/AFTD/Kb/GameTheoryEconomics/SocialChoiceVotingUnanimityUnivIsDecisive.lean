import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisive

/-!
# SocialChoice.Voting.unanimity_univ_isDecisive

Topic: social_choice   Node: 2f02c5d4d9fe

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.unanimity_univ_isDecisive`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.unanimity_univ_isDecisive
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.unanimity_univ_isDecisive [Fintype N] [Fintype A]
    {F : SWF N A} (h : SWF.Unanimity F) : IsDecisive F Set.univ := by
  intro a b P hP
  exact h P a b (fun i => hP i (by simp))
