import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismEfficientAllocation

/-!
# MultipleParameterMechanism.vcgPayment

Topic: mechanism_design   Node: 48f39201c40f

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.vcgPayment`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Clarke-pivot VCG payment charged to agent `i`: the best welfare that the other agents could get without `i`, minus the other agents' welfare at the efficient allocation chosen from all reports.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- The Clarke-pivot VCG payment charged to agent `i`: the best welfare that the other agents could get without `i`, minus the other agents' welfare at the efficient allocation chosen from all reports. -/
noncomputable def MultipleParameterMechanism.vcgPayment (v : ∀ _ : I, Valuation A ℝ) (i : I) : ℝ :=
  maxWelfareWithout v i - welfareWithout v i (efficientAllocation v)
