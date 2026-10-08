import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Relation.toLTS

Topic: computability   Node: 8bf7d2ca60be

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Relation.toLTS`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Relation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Any homogeneous relation can be seen as an LTS where all transitions have the same label.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- Any homogeneous relation can be seen as an LTS where all transitions have the same label. -/
def Cslib.LTS.Relation.toLTS [DecidableEq Label] (r : State → State → Prop) (μ : Label) :
  LTS State Label where
  Tr := fun s1 μ' s2 => if μ' = μ then r s1 s2 else False
