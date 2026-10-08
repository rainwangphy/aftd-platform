import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers

/-!
# MechanismWithTransfers.isExPostIR

Topic: mechanism_design   Node: 1b75da34ea1d

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.isExPostIR`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Ex-post individual rationality for a mechanism with transfers, relative to an externally supplied utility rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- Ex-post individual rationality for a mechanism with transfers, relative to an externally supplied utility rule. -/
def MechanismWithTransfers.isExPostIR [Preorder U] [Zero U]
    (u : A → (I → P) → (∀ i, T i) → I → U) : Prop :=
  ∀ trueTypes : (∀ i, T i), ∀ i : I, ∀ r : (∀ i, T i),
    0 ≤ u (M.allocationRule (Function.update r i (trueTypes i)))
      (M.paymentRule (Function.update r i (trueTypes i))) trueTypes i
