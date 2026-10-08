import AFTD.Prelude

/-!
# SocialChoice.Voting.tripleSet

Topic: social_choice   Node: 39da2ac3ffa1

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.tripleSet`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.tripleSet
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
def SocialChoice.Voting.tripleSet (a b c : A) : Set A :=
  {x | x = a ∨ x = b ∨ x = c}
