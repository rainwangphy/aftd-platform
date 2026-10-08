import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.updateProfile

Topic: social_choice   Node: 652376bf7de4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.updateProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Replace one voter's ballot.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Replace one voter's ballot. -/
@[reducible]
noncomputable def SocialChoice.Voting.updateProfile [Fintype N] [Fintype A]
    (P : Profile N A) (i : N) (r : LinearOrder A) : Profile N A := by
  classical
  exact { pref := fun j => if j = i then r else P.pref j }
