import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.BallotBottom

Topic: social_choice   Node: 7a2c90b62c85

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.BallotBottom`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A linear-order ballot ranks `a` last.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- A linear-order ballot ranks `a` last. -/
def SocialChoice.Voting.BallotBottom (r : LinearOrder A) (a : A) : Prop :=
  ∀ b : A, b ≠ a → BallotPrefers r b a
