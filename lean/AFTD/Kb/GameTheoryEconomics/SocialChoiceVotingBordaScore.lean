import AFTD.Prelude

/-!
# SocialChoice.Voting.bordaScore

Topic: social_choice   Node: bd2b3690c7d4

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.bordaScore`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Borda score vector, with top rank receiving `m - 1` points.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Borda score vector, with top rank receiving `m - 1` points. -/
def SocialChoice.Voting.bordaScore (m r : Nat) : Int :=
  Int.ofNat (m - 1 - r)
