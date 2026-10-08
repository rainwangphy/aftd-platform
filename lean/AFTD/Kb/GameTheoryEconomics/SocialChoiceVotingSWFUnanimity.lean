import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.Pref

/-!
# SocialChoice.Voting.SWF.Unanimity

Topic: social_choice   Node: a83205b9a4a9

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF.Unanimity`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Unanimity/Pareto for SWFs: unanimous strict preference forces social strict preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Unanimity/Pareto for SWFs: unanimous strict preference forces social strict preference. -/
def SocialChoice.Voting.SWF.Unanimity (F : SWF N A) : Prop :=
  ∀ (P : Profile N A) (a b : A),
    (∀ i : N, Prefers P i a b) → strict (F P) a b
