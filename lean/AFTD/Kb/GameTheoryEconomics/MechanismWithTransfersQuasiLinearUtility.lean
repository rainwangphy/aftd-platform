import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.Tcs.V

/-!
# MechanismWithTransfers.quasiLinearUtility

Topic: mechanism_design   Node: c840e63e2967

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.quasiLinearUtility`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Quasi-linear utility induced by: - a valuation function on allocations - an embedding of payments into utility space - subtraction in the utility space This permits, for example: - `V = U` with identity payment embedding - valuation codomains and payment codomains that differ but both map into `U`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- Quasi-linear utility induced by: - a valuation function on allocations - an embedding of payments into utility space - subtraction in the utility space This permits, for example: - `V = U` with identity payment embedding - valuation codomains and payment codomains that differ but both map into `U`. -/
def MechanismWithTransfers.quasiLinearUtility [Sub U]
    (val : A → (∀ i, T i) → I → V)
    (valueToUtility : V → U) (paymentToUtility : P → U)
    (r : ∀ i, T i) (trueTypes : ∀ i, T i) (i : I) : U :=
  valueToUtility (val (M.allocationRule r) trueTypes i) -
    paymentToUtility (M.paymentRule r i)
