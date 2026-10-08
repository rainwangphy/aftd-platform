import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripleSet

/-!
# SocialChoice.Voting.mem_triple_left

Topic: social_choice   Node: 1c5211e82fee

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.mem_triple_left`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.mem_triple_left
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.mem_triple_left (a b c : A) : a ∈ tripleSet a b c :=
  Or.inl rfl
