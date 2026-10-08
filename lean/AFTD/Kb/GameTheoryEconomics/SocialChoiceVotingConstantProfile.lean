import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.constantProfile

Topic: social_choice   Node: cb145594ef41

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.constantProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Constant profile where every voter submits the same ballot.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Constant profile where every voter submits the same ballot. -/
def SocialChoice.Voting.constantProfile [Fintype N] [Fintype A] (r : LinearOrder A) : Profile N A where
  pref := fun _ => r
