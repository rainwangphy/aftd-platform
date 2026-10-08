import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsExPostIR
import AFTD.Kb.Tcs.V

/-!
# MechanismWithTransfers.isQuasiLinearExPostIR

Topic: mechanism_design   Node: 00beb1fffde7

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.isQuasiLinearExPostIR`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ex-post IR for quasi-linear utility, as a specialization of `isExPostIR`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- Ex-post IR for quasi-linear utility, as a specialization of `isExPostIR`. -/
def MechanismWithTransfers.isQuasiLinearExPostIR [Sub U] [Preorder U] [Zero U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U) : Prop :=
  M.isExPostIR (fun a pay types i => valueToUtility (val a types i) - paymentToUtility (pay i))
