import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame

/-!
# MechanismWithTransfers.toStrategicGame

Topic: mechanism_design   Node: 564a8155dba7

Provenance: formalization of a published result. Source: EconCSLib, `MechanismWithTransfers.toStrategicGame`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 adapted; compiled here.

The strategic game induced by a transfer mechanism and an external utility rule. Utility is supplied as a function of: - allocation - payment vector - true type profile - agent index
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {T : I → Type*} {A P V U : Type*} in
variable (M : MechanismWithTransfers I T A P) in
/-- The strategic game induced by a transfer mechanism and an external utility rule. Utility is supplied as a function of: - allocation - payment vector - true type profile - agent index -/
def MechanismWithTransfers.toStrategicGame
    (u : A → (I → P) → (∀ i, T i) → I → U)
    (trueTypes : ∀ i, T i) : EconCSLib.StrategicGame I U where
  strategy := T
  payoff r i := u (M.allocationRule r) (M.paymentRule r) trueTypes i
