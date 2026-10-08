import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# MechanismWithTransfers.toQuasiLinearGame

Topic: mechanism_design   Node: db3d96d09779

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.toQuasiLinearGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The standard quasi-linear specialization of `toStrategicGame`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- The standard quasi-linear specialization of `toStrategicGame`. -/
def MechanismWithTransfers.toQuasiLinearGame [Sub U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U)
    (trueTypes : ∀ i, T i) : EconCSLib.StrategicGame I U :=
  M.toStrategicGame
    (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))
    trueTypes
