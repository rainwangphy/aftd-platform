import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct

/-!
# Cslib.CCS.Act.Co

Topic: distributed   Node: 148ce32c6ad2

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.Co`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Checks that an action is the coaction of another.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- Checks that an action is the coaction of another. -/
@[scoped grind]
inductive Cslib.CCS.Act.Co {Name : Type u} : Act Name → Act Name → Prop where
  | nc : Co (name a) (coname a)
  | cn : Co (coname a) (name a)
