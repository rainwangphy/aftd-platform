import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.IsDSIC

Topic: mechanism_design   Node: 2ace19e8f20b

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.IsDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Dominant-strategy incentive compatibility in the single-parameter, quasi-linear setting. Truthful reporting `θᵢ` is weakly dominant for every agent under utility `θᵢ * xᵢ(b) - pᵢ(b)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I : Type*} [DecidableEq I] {R : Type*} in
variable (M : SingleParameterMechanism I R) in
/-- Dominant-strategy incentive compatibility in the single-parameter, quasi-linear setting. Truthful reporting `θᵢ` is weakly dominant for every agent under utility `θᵢ * xᵢ(b) - pᵢ(b)`. -/
def SingleParameterMechanism.IsDSIC [Mul R] [Sub R] [Preorder R] : Prop :=
  ({ allocationRule := M.allocationRule
     paymentRule := M.paymentRule } :
    MechanismWithTransfers I (fun _ => R) (I → R) R).isDSIC
      (fun a pay types i => types i * a i - pay i)
