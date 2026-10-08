import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGame
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersToStrategicGame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameDeviate
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfile
import AFTD.Kb.GameTheoryEconomics.IsWeaklyDominant
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfersIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPayment
import AFTD.Kb.GameTheoryEconomics.WeaklyDominates
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.payment_sandwich

Topic: mechanism_design   Node: f8e897acbf2a

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment_sandwich`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

For a DSIC single-parameter mechanism, fixing all other bids yields the standard two-sided bound on payment differences.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- For a DSIC single-parameter mechanism, fixing all other bids yields the standard two-sided bound on payment differences. -/
theorem SingleParameterMechanism.payment_sandwich [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) (y z : ℝ) :
    z * (x (Function.update b i y) i - x (Function.update b i z) i) ≤
      p (Function.update b i y) i - p (Function.update b i z) i ∧
    p (Function.update b i y) i - p (Function.update b i z) i ≤
      y * (x (Function.update b i y) i - x (Function.update b i z) i) := by
  let vy : I → ℝ := Function.update b i y
  have h1 : y * x (Function.update b i z) i - p (Function.update b i z) i ≤
      y * x (Function.update b i y) i - p (Function.update b i y) i := by
    have := hdsic vy i z b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, vy]
      using this
  let vz : I → ℝ := Function.update b i z
  have h2 : z * x (Function.update b i y) i - p (Function.update b i y) i ≤
      z * x (Function.update b i z) i - p (Function.update b i z) i := by
    have := hdsic vz i y b
    simpa [SingleParameterMechanism.IsDSIC, MechanismWithTransfers.isDSIC,
      MechanismWithTransfers.toStrategicGame, IsWeaklyDominant, WeaklyDominates,
      SingleParameterMechanism.payment, vz]
      using this
  constructor <;> linarith
