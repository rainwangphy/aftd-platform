import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWFDictatorial

/-!
# SocialChoice.Voting.SWF.NonDictatorial

Topic: social_choice   Node: 70b7da568d47

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF.NonDictatorial`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A SWF is non-dictatorial.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- A SWF is non-dictatorial. -/
def SocialChoice.Voting.SWF.NonDictatorial (F : SWF N A) : Prop :=
  ¬ Dictatorial F
