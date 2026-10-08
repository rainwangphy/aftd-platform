import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismExistsEfficientAllocation

/-!
# MultipleParameterMechanism.efficientAllocation_isOptimal

Topic: mechanism_design   Node: 6d4be2f957f8

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.efficientAllocation_isOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The chosen VCG allocation maximizes reported social welfare.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
/-- The chosen VCG allocation maximizes reported social welfare. -/
lemma MultipleParameterMechanism.efficientAllocation_isOptimal (v : ∀ _ : I, Valuation A ℝ) (a : A) :
    socialWelfare v a ≤ socialWelfare v (efficientAllocation v) :=
  Classical.choose_spec (exists_efficientAllocation v) a
