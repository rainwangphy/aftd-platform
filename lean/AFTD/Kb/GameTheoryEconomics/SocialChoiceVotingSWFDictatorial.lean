import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.F
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.SWF.Dictatorial

Topic: social_choice   Node: ed5581a2e9f5

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF.Dictatorial`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A SWF is dictatorial if one voter always determines every strict social comparison.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- A SWF is dictatorial if one voter always determines every strict social comparison. -/
def SocialChoice.Voting.SWF.Dictatorial (F : SWF N A) : Prop :=
  ∃ i : N, ∀ (P : Profile N A) (a b : A),
    Prefers P i a b → strict (F P) a b
