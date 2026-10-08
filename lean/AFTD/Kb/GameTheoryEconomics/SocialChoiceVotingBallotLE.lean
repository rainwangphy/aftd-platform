import AFTD.Prelude

/-!
# SocialChoice.Voting.ballotLE

Topic: social_choice   Node: a17a252673e3

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.ballotLE`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ballot `r` ranks `a` strictly above `b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Ballot `r` ranks `a` strictly above `b`. -/
abbrev SocialChoice.Voting.ballotLE (r : LinearOrder A) : LE A :=
  @Preorder.toLE A (@PartialOrder.toPreorder A (@LinearOrder.toPartialOrder A r))
