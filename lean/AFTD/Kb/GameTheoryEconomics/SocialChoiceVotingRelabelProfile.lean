import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingProfile
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingRelabelBallotEquiv

/-!
# SocialChoice.Voting.relabelProfile

Topic: social_choice   Node: 61fe1a0d84e3

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.relabelProfile`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relabel a profile along an equivalence of alternative types.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Relabel a profile along an equivalence of alternative types. -/
noncomputable def SocialChoice.Voting.relabelProfile {B : Type*} [Fintype N] [Fintype A] [Fintype B]
    (P : Profile N A) (e : A ≃ B) : Profile N B where
  pref := fun i => relabelBallotEquiv (P.pref i) e
