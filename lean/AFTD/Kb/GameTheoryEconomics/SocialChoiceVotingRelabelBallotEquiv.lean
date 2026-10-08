import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotFromInjective
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.relabelBallotEquiv

Topic: social_choice   Node: f2b65fc05d9a

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.relabelBallotEquiv`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relabel a linear order along an equivalence of alternative types.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Relabel a linear order along an equivalence of alternative types. -/
noncomputable def SocialChoice.Voting.relabelBallotEquiv {B : Type*} (r : LinearOrder A) (e : A ≃ B) :
    LinearOrder B := by
  classical
  exact ballotFromInjective r e.symm e.symm.injective
