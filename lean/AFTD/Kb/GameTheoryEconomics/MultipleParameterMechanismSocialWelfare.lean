import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation

/-!
# MultipleParameterMechanism.socialWelfare

Topic: mechanism_design   Node: 2153c15aee1a

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.socialWelfare`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/VCG.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Reported social welfare of allocation `a` under a profile of valuations.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators in
variable {I A : Type*} [Fintype I] [Fintype A] [Nonempty A] in
/-- Reported social welfare of allocation `a` under a profile of valuations. -/
def MultipleParameterMechanism.socialWelfare (v : ∀ _ : I, Valuation A ℝ) (a : A) : ℝ :=
  ∑ i, v i a
