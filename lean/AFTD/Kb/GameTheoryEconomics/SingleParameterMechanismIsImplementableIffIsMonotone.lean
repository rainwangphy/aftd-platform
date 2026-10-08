import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsImplementable
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotone
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsMonotoneOfIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsImplementableOfIsMonotone
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.isImplementable_iff_isMonotone

Topic: mechanism_design   Node: df4577ed1741

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.isImplementable_iff_isMonotone`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Myerson Lemma `(a)`: an allocation rule is implementable if and only if it is monotone.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma `(a)`: an allocation rule is implementable if and only if it is monotone. -/
theorem SingleParameterMechanism.isImplementable_iff_isMonotone [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) :
    IsImplementable x ↔
      IsMonotone ({ allocationRule := x, paymentRule := myersonPayment x } :
        SingleParameterMechanism I ℝ) := by
  constructor
  · intro hx
    rcases hx with ⟨p, hp⟩
    simpa [SingleParameterMechanism.IsMonotone] using
      (isMonotone_of_isDSIC (M := ({ allocationRule := x, paymentRule := p } :
        SingleParameterMechanism I ℝ)) hp)
  · intro hx
    exact isImplementable_of_isMonotone hx
