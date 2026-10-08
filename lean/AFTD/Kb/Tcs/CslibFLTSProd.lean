import AFTD.Prelude
import AFTD.Kb.Tcs.CslibFLTS

/-!
# Cslib.FLTS.prod

Topic: computability   Node: 761b5bc417f1

Provenance: formalization of a published result. Source: CSLib, `Cslib.FLTS.prod`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/FLTS/Prod.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The product of two FLTS with the same label type.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- The product of two FLTS with the same label type. -/
@[scoped grind =]
def Cslib.FLTS.prod (flts1 : FLTS State1 Label) (flts2 : FLTS State2 Label) :
    FLTS (State1 × State2) Label where
  tr := fun (s1, s2) μ ↦ (flts1.tr s1 μ, flts2.tr s2 μ)
