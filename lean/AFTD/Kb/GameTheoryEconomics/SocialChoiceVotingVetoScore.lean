import AFTD.Prelude

/-!
# SocialChoice.Voting.vetoScore

Topic: social_choice   Node: 0fdf3439fa07

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.vetoScore`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Veto score vector: every non-last rank receives one point.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- Veto score vector: every non-last rank receives one point. -/
def SocialChoice.Voting.vetoScore (m r : Nat) : Int :=
  if r + 1 = m then 0 else 1
