import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Strict
import AFTD.Kb.GameTheoryEconomics.Profile

/-!
# SocialChoice.Voting.Profile

Topic: social_choice   Node: 58949a5f8343

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.Profile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A voting profile assigns each voter a strict linear order over alternatives.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A voting profile assigns each voter a strict linear order over alternatives. -/
structure SocialChoice.Voting.Profile (N A : Type*) [Fintype N] [Fintype A] where
  /-- The ballot submitted by each voter. Smaller means more preferred. -/
  pref : N → LinearOrder A
