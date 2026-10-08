import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.Profile.ext

Topic: social_choice   Node: 3915de23328e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Profile.ext`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.Profile.ext
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
@[ext]
theorem SocialChoice.Voting.Profile.ext [Fintype N] [Fintype A] {P Q : Profile N A}
    (h : ∀ i : N, P.pref i = Q.pref i) : P = Q := by
  cases P
  cases Q
  simp only at h
  exact congrArg Profile.mk (funext h)
