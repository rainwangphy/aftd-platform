import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation

/-!
# MultipleParameterMechanism.welfareWithout

Topic: mechanism_design   Node: 1fa0cd4d5fc3

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.welfareWithout`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reported social welfare of all agents except `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- Reported social welfare of all agents except `i`. -/
def MultipleParameterMechanism.welfareWithout (v : ∀ _ : I, Valuation A ℝ) (i : I) (a : A) : ℝ :=
  (Finset.univ.erase i).sum fun j => v j a
