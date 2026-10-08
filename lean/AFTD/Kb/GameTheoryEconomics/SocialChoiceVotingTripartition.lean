import AFTD.Prelude

/-!
# SocialChoice.Voting.tripartition

Topic: social_choice   Node: 3bdea3420941

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.tripartition`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Decisive.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.tripartition
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
def SocialChoice.Voting.tripartition {N : Type*} (A B C : Set N) : Prop :=
  (A ∩ B = ∅) ∧ (A ∩ C = ∅) ∧ (B ∩ C = ∅) ∧ (A ∪ B ∪ C = Set.univ)
