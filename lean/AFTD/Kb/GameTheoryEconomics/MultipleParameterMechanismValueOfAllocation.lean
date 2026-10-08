import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MultipleParameterMechanismValuation
import AFTD.Kb.Tcs.V

/-!
# MultipleParameterMechanism.valueOfAllocation

Topic: mechanism_design   Node: c00aaa077a0e

Provenance: formalization of a published result. Source: EconCSLib, `MultipleParameterMechanism.valueOfAllocation`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/Transfer.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The value extractor used by the generic quasi-linear transfer definitions: agent `i` evaluates allocation `a` by applying their valuation function to `a`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {I A V : Type*} in
/-- The value extractor used by the generic quasi-linear transfer definitions: agent `i` evaluates allocation `a` by applying their valuation function to `a`. -/
def MultipleParameterMechanism.valueOfAllocation
    (a : A) (types : ∀ _ : I, Valuation A V) (i : I) : V :=
  types i a
