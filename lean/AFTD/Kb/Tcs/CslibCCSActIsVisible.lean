import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct

/-!
# Cslib.CCS.Act.IsVisible

Topic: distributed   Node: d13dfd170bbf

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.IsVisible`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An action is visible if it a name or a coname.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- An action is visible if it a name or a coname. -/
@[scoped grind]
inductive Cslib.CCS.Act.IsVisible : Act Name → Prop where
  | name : IsVisible (Act.name a)
  | coname : IsVisible (Act.coname a)
