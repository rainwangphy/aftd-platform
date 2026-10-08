import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismWelfareWithout

/-!
# MultipleParameterMechanism.maxWelfareWithout

Topic: mechanism_design   Node: 9463d9a89965

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.maxWelfareWithout`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The maximum reported welfare of agents other than `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
variable [DecidableEq I] in
/-- The maximum reported welfare of agents other than `i`. -/
noncomputable def MultipleParameterMechanism.maxWelfareWithout (v : ∀ _ : I, Valuation A ℝ) (i : I) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (welfareWithout v i)
