import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPayment
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsDSIC
import AFTD.Kb.GameTheoryEconomics.WeaklyDominates
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.isMonotone_of_isDSIC

Topic: mechanism_design   Node: 6ed6b076f313

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.isMonotone_of_isDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Myerson Lemma, Property 1: every DSIC single-parameter mechanism has a monotone allocation rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma, Property 1: every DSIC single-parameter mechanism has a monotone allocation rule. -/
theorem SingleParameterMechanism.isMonotone_of_isDSIC [DecidableEq I] {M : SingleParameterMechanism I ℝ}
    (hdsic : M.IsDSIC) :
    M.IsMonotone := by
  intro i θ θ' hθ b
  by_cases hEq : θ = θ'
  · simp [hEq]
  have hlt : θ < θ' := lt_of_le_of_ne hθ hEq
  let v : I → ℝ := Function.update b i θ
  let v' : I → ℝ := Function.update b i θ'
  have h1 : θ * M.allocationRule (Function.update b i θ') i -
      M.payment (Function.update b i θ') i ≤
      θ * M.allocationRule (Function.update b i θ) i -
      M.payment (Function.update b i θ) i := by
    have := hdsic v i θ' b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, v]
      using this
  have h2 : θ' * M.allocationRule (Function.update b i θ) i -
      M.payment (Function.update b i θ) i ≤
      θ' * M.allocationRule (Function.update b i θ') i -
      M.payment (Function.update b i θ') i := by
    have := hdsic v' i θ b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, v']
      using this
  nlinarith
