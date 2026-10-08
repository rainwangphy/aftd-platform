import AFTD.Prelude

/-!
# SocialChoice.Voting.ballotLT

Topic: social_choice   Node: d1ae8981869d

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.ballotLT`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ballot `r`'s strict-order instance, exposed explicitly to avoid ambient typeclass search.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Ballot `r`'s strict-order instance, exposed explicitly to avoid ambient typeclass search. -/
abbrev SocialChoice.Voting.ballotLT (r : LinearOrder A) : LT A :=
  @Preorder.toLT A (@PartialOrder.toPreorder A (@LinearOrder.toPartialOrder A r))
