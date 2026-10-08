import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismQuasiLinearUtility
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismWithMyersonPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPayment
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismQuasiLinearValue
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismMyersonPayment

/-!
# SingleParameterMechanism.withMyersonPayment_quasiLinearUtility_eq

Topic: mechanism_design   Node: 337f48b6a893

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.withMyersonPayment_quasiLinearUtility_eq`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Utility under the canonical Myerson payment rule can be written in the standard envelope-friendly form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Utility under the canonical Myerson payment rule can be written in the standard envelope-friendly form. -/
lemma SingleParameterMechanism.withMyersonPayment_quasiLinearUtility_eq [DecidableEq I]
    (x : (I → ℝ) → I → ℝ) (v b : I → ℝ) (i : I) :
    (withMyersonPayment x).quasiLinearUtility b v i =
      (v i - b i) * x b i + ∫ z in 0..b i, x (Function.update b i z) i := by
  simp [SingleParameterMechanism.quasiLinearUtility, SingleParameterMechanism.quasiLinearValue,
    SingleParameterMechanism.payment, withMyersonPayment, myersonPayment]
  ring
