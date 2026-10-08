import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWithoutAllocation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismExistsWithoutAllocation

/-!
# MultipleParameterMechanism.withoutAllocation_isOptimal

Topic: mechanism_design   Node: 68720d3451e2

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.withoutAllocation_isOptimal`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The chosen allocation without agent `i` maximizes the reported welfare of the other agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- The chosen allocation without agent `i` maximizes the reported welfare of the other agents. -/
lemma MultipleParameterMechanism.withoutAllocation_isOptimal (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) :
    welfareWithout v i a ≤ welfareWithout v i (withoutAllocation v i) :=
  Classical.choose_spec (exists_withoutAllocation v i) a
