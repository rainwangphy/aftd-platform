import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.hybridProfile

Topic: social_choice   Node: cb6ea19efcea

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.hybridProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.hybridProfile
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
@[reducible]
noncomputable def SocialChoice.Voting.hybridProfile [Fintype N] [DecidableEq N] [Fintype A]
    (P Q : Profile N A) (S : Finset N) : Profile N A where
  pref := fun i => if i ∈ S then Q.pref i else P.pref i
