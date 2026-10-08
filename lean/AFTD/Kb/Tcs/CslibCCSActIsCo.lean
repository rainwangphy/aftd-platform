import AFTD.Prelude
import AFTD.Kb.Tcs.CslibCCSAct

/-!
# Cslib.CCS.Act.isCo

Topic: distributed   Node: c93cd595bbb1

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act.isCo`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Checks that an action is the coaction of another. This is the Boolean version of `Act.Co`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- Checks that an action is the coaction of another. This is the Boolean version of `Act.Co`. -/
@[scoped grind =]
def Cslib.CCS.Act.isCo [DecidableEq Name] (μ μ' : Act Name) : Bool :=
  match μ, μ' with
  | name a, coname b | coname a, name b => a = b
  | _, _ => false
