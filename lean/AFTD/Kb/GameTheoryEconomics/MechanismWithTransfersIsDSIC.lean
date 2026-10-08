import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# MechanismWithTransfers.isDSIC

Topic: mechanism_design   Node: beca24c41edd

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.isDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

DSIC for a mechanism with transfers, relative to an externally supplied utility rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MechanismWithTransfers in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- DSIC for a mechanism with transfers, relative to an externally supplied utility rule. -/
def MechanismWithTransfers.isDSIC [Preorder U]
    (u : A → (I → P) → (∀ i, T i) → I → U) : Prop :=
  ∀ trueTypes : (∀ i, T i), ∀ i : I,
    IsWeaklyDominant (M.toStrategicGame u trueTypes) i (trueTypes i)
