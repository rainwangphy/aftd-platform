import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile

/-!
# SocialChoice.Voting.VotingRule

Topic: social_choice   Node: d4fa5c2ce3cb

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.VotingRule`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A set-valued voting rule on fixed finite voter and candidate types.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A set-valued voting rule on fixed finite voter and candidate types. -/
abbrev SocialChoice.Voting.VotingRule (N A : Type*) [Fintype N] [Fintype A] :=
  Profile N A → Finset A
