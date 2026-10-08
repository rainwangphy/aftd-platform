import AFTD.Prelude

/-!
# SocialChoice.Voting.permuteWinners

Topic: social_choice   Node: babc841ddf54

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.permuteWinners`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Candidate renaming on winner sets.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
variable [Fintype N] [Fintype A] in
/-- Candidate renaming on winner sets. -/
noncomputable def SocialChoice.Voting.permuteWinners (σ : Equiv.Perm A) (s : Finset A) : Finset A := by
  classical
  exact s.map σ.toEmbedding
