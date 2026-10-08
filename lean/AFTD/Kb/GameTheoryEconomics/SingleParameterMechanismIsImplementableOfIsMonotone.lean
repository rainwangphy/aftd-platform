import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsImplementable
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPaymentIsDSICOfIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.isImplementable_of_isMonotone

Topic: mechanism_design   Node: cfba26320768

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.isImplementable_of_isMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Myerson Lemma, Property 2, reformulated: an allocation rule is implementable if it is monotone.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma, Property 2, reformulated: an allocation rule is implementable if it is monotone. -/
theorem SingleParameterMechanism.isImplementable_of_isMonotone [DecidableEq I]
    {x : (I → ℝ) → I → ℝ}
    (hx : IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
      SingleParameterMechanism I ℝ)) :
    IsImplementable x := by
  refine ⟨myersonPayment x, ?_⟩
  simpa [withMyersonPayment] using withMyersonPayment_isDSIC_of_isMonotone hx
