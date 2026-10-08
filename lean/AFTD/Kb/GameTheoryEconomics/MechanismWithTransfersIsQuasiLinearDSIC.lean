import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsDSIC
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe
import AFTD.Kb.Tcs.V

/-!
# MechanismWithTransfers.isQuasiLinearDSIC

Topic: mechanism_design   Node: 443071554cdf

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.isQuasiLinearDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

DSIC for quasi-linear utility, as a specialization of `isDSIC`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MechanismWithTransfers in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- DSIC for quasi-linear utility, as a specialization of `isDSIC`. -/
def MechanismWithTransfers.isQuasiLinearDSIC [Sub U] [Preorder U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U) : Prop :=
  M.isDSIC (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))
