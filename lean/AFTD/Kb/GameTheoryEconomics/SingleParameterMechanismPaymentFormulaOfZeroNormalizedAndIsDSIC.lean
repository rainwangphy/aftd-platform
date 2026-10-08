import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismZeroNormalized
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismIsDSIC
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanism
import AFTD.Kb.GameTheoryEconomics.MechanismWithTransfers
import AFTD.Kb.GameTheoryEconomics.SingleParameterMechanismPaymentFormulaOfIsDSICOfZeroNormalized
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSelf
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateSame
import AFTD.Kb.GameTheoryEconomics.EconCSLibStrategicGameProfileDeviateOfNe

/-!
# SingleParameterMechanism.payment_formula_of_zeroNormalized_and_isDSIC

Topic: mechanism_design   Node: f3489a8d195c

Provenance: formalization of a published result. Source: EconCSLib, `SingleParameterMechanism.payment_formula_of_zeroNormalized_and_isDSIC`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Myerson.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Myerson Lemma `(c)`: the unique zero-normalized DSIC payment rule from `(b)` is given by the explicit formula `bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SingleParameterMechanism in
variable {I : Type*} in
/-- Myerson Lemma `(c)`: the unique zero-normalized DSIC payment rule from `(b)` is given by the explicit formula `bᵢ xᵢ(b) - ∫₀^{bᵢ} xᵢ(z, b₋ᵢ) dz`. -/
theorem SingleParameterMechanism.payment_formula_of_zeroNormalized_and_isDSIC [DecidableEq I]
    {x p : (I → ℝ) → I → ℝ}
    (hp : ZeroNormalized p ∧
      ({ allocationRule := x, paymentRule := p } : SingleParameterMechanism I ℝ).IsDSIC)
    (b : I → ℝ) (i : I) :
    p b i = b i * x b i - ∫ z in 0..b i, x (Function.update b i z) i :=
  payment_formula_of_isDSIC_of_zeroNormalized hp.2 hp.1 b i
