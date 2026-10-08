import AFTD.Prelude

/-!
# SocialChoice.Voting.pluralityScore

Topic: social_choice   Node: e379f80dfa44

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.pluralityScore`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Plurality score vector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Plurality score vector. -/
def SocialChoice.Voting.pluralityScore (_m r : Nat) : Int :=
  if r = 0 then 1 else 0
