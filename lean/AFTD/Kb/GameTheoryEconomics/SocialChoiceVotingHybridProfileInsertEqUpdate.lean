import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingHybridProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingUpdateProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfileExt
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.hybridProfile_insert_eq_update

Topic: social_choice   Node: c1531c2b52bd

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.hybridProfile_insert_eq_update`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.hybridProfile_insert_eq_update
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.hybridProfile_insert_eq_update [Fintype N] [DecidableEq N] [Fintype A]
    (P Q : Profile N A) (S : Finset N) {i : N} (hi : i ∉ S) :
    hybridProfile P Q (insert i S) = updateProfile (hybridProfile P Q S) i (Q.pref i) := by
  classical
  apply Profile.ext
  intro j
  by_cases hji : j = i
  · subst hji
    simp [hi]
  · simp [hji]
