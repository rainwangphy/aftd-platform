import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisiveFor
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsWeaklyDecisiveFor

/-!
# SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor

Topic: social_choice   Node: b8ca1698cf5c

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.isWeaklyDecisiveFor_of_isDecisiveFor [Fintype N] [Fintype A]
    {F : SWF N A} {C : Set N} {a b : A}
    (h : IsDecisiveFor F C a b) : IsWeaklyDecisiveFor F C a b := by
  intro P hP
  exact h P hP.left
