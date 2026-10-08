import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFIsDictator
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFUnanimity
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF

/-!
# SocialChoice.Voting.singleton_unanimity_isDictator

Topic: social_choice   Node: b6111ae31b19

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.singleton_unanimity_isDictator`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.singleton_unanimity_isDictator
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.singleton_unanimity_isDictator [Fintype N] [Fintype A] [Subsingleton N]
    {F : SWF N A} (h : SWF.Unanimity F) (i : N) :
    F.IsDictator i := by
  intro a b P hi
  apply h
  intro j
  rw [← Subsingleton.allEq i j]
  exact hi i rfl
