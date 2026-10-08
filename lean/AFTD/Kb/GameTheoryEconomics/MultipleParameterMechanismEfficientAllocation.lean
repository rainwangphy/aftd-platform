import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismExistsEfficientAllocation

/-!
# MultipleParameterMechanism.efficientAllocation

Topic: mechanism_design   Node: d4852410d6ad

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.efficientAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A welfare-maximizing allocation, chosen noncomputably from finite `A`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
/-- A welfare-maximizing allocation, chosen noncomputably from finite `A`. -/
noncomputable def MultipleParameterMechanism.efficientAllocation (v : ∀ _ : I, Valuation A ℝ) : A :=
  Classical.choose (exists_efficientAllocation v)
