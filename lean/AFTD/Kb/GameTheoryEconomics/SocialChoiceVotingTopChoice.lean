import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.topChoice

Topic: social_choice   Node: d64f02b6a1cb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.topChoice`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The top-ranked alternative of voter `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- The top-ranked alternative of voter `i`. -/
noncomputable def SocialChoice.Voting.topChoice [Fintype N] [Fintype A] [Nonempty A]
    (P : Profile N A) (i : N) : A := by
  classical
  letI := P.pref i
  exact Finset.min' Finset.univ Finset.univ_nonempty
