import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefers
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotPrefersBallotFromInjective

/-!
# SocialChoice.Voting.rank

Topic: social_choice   Node: b8fe967fe163

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.rank`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/VotingRules.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`rank r a` is the number of alternatives strictly above `a` in ballot `r`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
open Finset in
open scoped BigOperators in
variable {N A : Type*} in
/-- `rank r a` is the number of alternatives strictly above `a` in ballot `r`. -/
noncomputable def SocialChoice.Voting.rank [Fintype A] (r : LinearOrder A) (a : A) : Nat :=
  Finset.card (Finset.univ.filter (fun b => BallotPrefers r b a))
