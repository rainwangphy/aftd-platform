import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingSWF
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.Tcs.F
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.SWF.IIA

Topic: social_choice   Node: 4fa08ca223b4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF.IIA`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Independence of irrelevant alternatives for SWFs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Independence of irrelevant alternatives for SWFs. -/
def SocialChoice.Voting.SWF.IIA (F : SWF N A) : Prop :=
  ∀ (P Q : Profile N A) (a b : A),
    (∀ i : N, Prefers P i a b ↔ Prefers Q i a b) →
    (F P a b ↔ F Q a b)
