import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersTotalOfNe

/-!
# SocialChoice.Voting.Prefers.total_of_ne

Topic: social_choice   Node: 48bd11fa8b17

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Prefers.total_of_ne`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.Prefers.total_of_ne
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
theorem SocialChoice.Voting.Prefers.total_of_ne [Fintype N] [Fintype A] (P : Profile N A) (i : N)
    {a b : A} (hne : a ≠ b) : Prefers P i a b ∨ Prefers P i b a :=
  BallotPrefers.total_of_ne (P.pref i) hne
