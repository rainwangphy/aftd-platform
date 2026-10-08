import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismMaxWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithoutUpdateSelf

/-!
# MultipleParameterMechanism.maxWelfareWithout_update_self

Topic: mechanism_design   Node: 3a595f6e3bb1

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.maxWelfareWithout_update_self`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Changing agent `i`'s report does not change the maximum welfare achievable by the other agents.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- Changing agent `i`'s report does not change the maximum welfare achievable by the other agents. -/
lemma MultipleParameterMechanism.maxWelfareWithout_update_self
    (v : ∀ _ : I, Valuation A ℝ) (i : I) (report : Valuation A ℝ) :
    maxWelfareWithout (Function.update v i report) i = maxWelfareWithout v i := by
  rw [maxWelfareWithout, maxWelfareWithout]
  exact Finset.sup'_congr Finset.univ_nonempty rfl
    (fun a _ => welfareWithout_update_self v i report a)
