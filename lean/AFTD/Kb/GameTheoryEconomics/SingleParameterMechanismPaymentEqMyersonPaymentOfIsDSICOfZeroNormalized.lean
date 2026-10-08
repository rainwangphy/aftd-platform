import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismZeroNormalized
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPaymentFormulaOfIsDSICOfZeroNormalized
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized

Topic: mechanism_design   Node: 44e294522057

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Uniqueness of zero-normalized DSIC payment rules: among zero-normalized payment rules, the canonical Myerson payment rule is the unique one that implements a monotone allocation rule.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Uniqueness of zero-normalized DSIC payment rules: among zero-normalized payment rules, the canonical Myerson payment rule is the unique one that implements a monotone allocation rule. -/
theorem SingleParameterMechanism.payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (h0 : ZeroNormalized p) :
    p = myersonPayment x := by
  funext b i
  simpa [myersonPayment] using payment_formula_of_isDSIC_of_zeroNormalized hdsic h0 b i
