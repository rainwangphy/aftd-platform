import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingIsDecisive

/-!
# SocialChoice.Voting.SWF.IsDictator

Topic: social_choice   Node: 27f2fc660d1f

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF.IsDictator`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An individual is a dictator exactly when their singleton coalition is decisive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
/-- An individual is a dictator exactly when their singleton coalition is decisive. -/
def SocialChoice.Voting.SWF.IsDictator [Fintype N] [Fintype A] (F : SWF N A) (i : N) : Prop :=
  IsDecisive F {i}
