import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.Pref
import AFTD.Kb.GameTheoryEconomics.InstCoeFunPrefForallForallProp
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.SWF

Topic: social_choice   Node: ae75db294242

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.SWF`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A social welfare function maps strict profiles to a weak social preference.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A social welfare function maps strict profiles to a weak social preference. -/
abbrev SocialChoice.Voting.SWF (N A : Type*) [Fintype N] [Fintype A] :=
  Profile N A → Pref A
