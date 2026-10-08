import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.union

Topic: computability   Node: 5ec89c2717d3

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.union`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Union.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The union of two LTSs defined on the same types.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
variable {State : Type u} {Label : Type v} in
/-- The union of two LTSs defined on the same types. -/
def Cslib.LTS.union (lts1 lts2 : LTS State Label) : LTS State Label where
  Tr := lts1.Tr ⊔ lts2.Tr
