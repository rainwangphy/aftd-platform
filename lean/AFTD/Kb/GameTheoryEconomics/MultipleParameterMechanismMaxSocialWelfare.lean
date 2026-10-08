import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismSocialWelfare

/-!
# MultipleParameterMechanism.maxSocialWelfare

Topic: mechanism_design   Node: 9681126831d0

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.maxSocialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The maximum reported social welfare over all allocations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
/-- The maximum reported social welfare over all allocations. -/
noncomputable def MultipleParameterMechanism.maxSocialWelfare (v : ∀ _ : I, Valuation A ℝ) : ℝ :=
  Finset.sup' Finset.univ Finset.univ_nonempty (socialWelfare v)
