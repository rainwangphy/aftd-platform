import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPaymentSandwich
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.payment_difference_bound

Topic: mechanism_design   Node: 18c16654f327

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment_difference_bound`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If two payment rules implement the same allocation rule in DSIC form, then their difference along a one-dimensional deviation is controlled by the change in the allocation rule. This is the comparison estimate used in the proof of the Myerson payment identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- If two payment rules implement the same allocation rule in DSIC form, then their difference along a one-dimensional deviation is controlled by the change in the allocation rule. This is the comparison estimate used in the proof of the Myerson payment identity. -/
theorem SingleParameterMechanism.payment_difference_bound [DecidableEq I]
    {x p q : (I → ℝ) → I → ℝ}
    (hpdsic : ({ allocationRule := x, paymentRule := p } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (hqdsic : ({ allocationRule := x, paymentRule := q } :
      SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) (y z : ℝ) :
    |(p (Function.update b i y) i - q (Function.update b i y) i) -
        (p (Function.update b i z) i - q (Function.update b i z) i)| ≤
      (y - z) * (x (Function.update b i y) i - x (Function.update b i z) i) := by
  obtain ⟨hp₁, hp₂⟩ := payment_sandwich hpdsic b i y z
  obtain ⟨hq₁, hq₂⟩ := payment_sandwich hqdsic b i y z
  rw [abs_le]
  constructor <;> linarith
