import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingTripleSet

/-!
# SocialChoice.Voting.mem_triple_mid

Topic: social_choice   Node: 90e5fd4e013e

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.mem_triple_mid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/GibbardSatterthwaite.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SocialChoice.Voting.mem_triple_mid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {N A : Type*} in
theorem SocialChoice.Voting.mem_triple_mid (a b c : A) : b ∈ tripleSet a b c :=
  Or.inr (Or.inl rfl)
