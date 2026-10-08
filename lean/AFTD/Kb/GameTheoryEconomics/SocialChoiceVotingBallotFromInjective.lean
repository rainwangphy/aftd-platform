import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLE
import AFTD.Kb.GameTheoryEconomics.SocialChoiceVotingBallotLT

/-!
# SocialChoice.Voting.ballotFromInjective

Topic: social_choice   Node: 80fe6e005170

Provenance: formalization of a published result. Source: EconCSLib, `SocialChoice.Voting.ballotFromInjective`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/SocialChoice/Voting/Basic.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pull a linear order back along an injective map, using the supplied codomain order explicitly rather than relying on ambient typeclass search. This is the safe constructor for ballots on types such as `Fin n`, which already carry a default order.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset in
variable {N A : Type*} in
/-- Pull a linear order back along an injective map, using the supplied codomain order explicitly rather than relying on ambient typeclass search. This is the safe constructor for ballots on types such as `Fin n`, which already carry a default order. -/
noncomputable def SocialChoice.Voting.ballotFromInjective {B : Type*} (rB : LinearOrder B)
    (f : A → B) (hf : Function.Injective f) : LinearOrder A where
  toPartialOrder :=
    { toPreorder :=
        { toLE := ⟨fun a b => @LE.le B (ballotLE rB) (f a) (f b)⟩
          toLT := ⟨fun a b => @LT.lt B (ballotLT rB) (f a) (f b)⟩
          le_refl := fun a => rB.le_refl (f a)
          le_trans := fun a b c hab hbc => rB.le_trans (f a) (f b) (f c) hab hbc
          lt_iff_le_not_ge := fun a b => rB.lt_iff_le_not_ge (f a) (f b) }
      le_antisymm := fun a b hab hba => hf (rB.le_antisymm (f a) (f b) hab hba) }
  toMin := ⟨fun a b =>
    if @LE.le B (ballotLE rB) (f a) (f b) then a else b⟩
  toMax := ⟨fun a b =>
    if @LE.le B (ballotLE rB) (f a) (f b) then b else a⟩
  le_total := fun a b => rB.le_total (f a) (f b)
  toDecidableLE := fun a b =>
    @LinearOrder.toDecidableLE B rB (f a) (f b)
  toDecidableEq := Classical.decEq A
  toDecidableLT := fun a b =>
    @LinearOrder.toDecidableLT B rB (f a) (f b)
  min_def := by
    intro a b
    rfl
  max_def := by
    intro a b
    rfl
