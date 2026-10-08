import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout

/-!
# MultipleParameterMechanism.welfareWithout_update_self

Topic: mechanism_design   Node: 21483b3c7f47

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.welfareWithout_update_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Changing agent `i`'s report does not change the welfare of agents other than `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
omit [Fintype A] [Nonempty A] in
/-- Changing agent `i`'s report does not change the welfare of agents other than `i`. -/
lemma MultipleParameterMechanism.welfareWithout_update_self
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (report : Valuation A ℝ) (a : A) :
    welfareWithout (Function.update v i report) i a = welfareWithout v i a := by
  rw [welfareWithout, welfareWithout]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    simpa using hj
  simp [Function.update, hji]
