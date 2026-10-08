import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismZeroNormalized
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPaymentZeroNormalized
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPaymentIsDSICOfIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPaymentEqMyersonPaymentOfIsDSICOfZeroNormalized
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone

Topic: mechanism_design   Node: 5f2ed2292de6

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Myerson Lemma `(b)`: if `x` is monotone, then there is a unique zero-normalized payment rule making `(x, p)` DSIC.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma `(b)`: if `x` is monotone, then there is a unique zero-normalized payment rule making `(x, p)` DSIC. -/
theorem SingleParameterMechanism.existsUnique_zeroNormalized_payment_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    ∃! p : (I → ℝ) → I → ℝ,
      ZeroNormalized p ∧
        ({ allocationRule := x, paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC := by
  refine ⟨myersonPayment x, ?_, ?_⟩
  · exact ⟨myersonPayment_zeroNormalized x, withMyersonPayment_isDSIC_of_isMonotone hx⟩
  · intro p hp
    exact payment_eq_myersonPayment_of_isDSIC_of_zeroNormalized hp.2 hp.1
