import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.permuteVoters

Topic: social_choice   Node: 436389e30085

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.permuteVoters`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relabel voters by a permutation of the electorate.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Relabel voters by a permutation of the electorate. -/
def SocialChoice.Voting.permuteVoters [Fintype N] [Fintype A]
    (P : Profile N A) (σ : Equiv.Perm N) : Profile N A where
  pref := fun i => P.pref (σ i)
