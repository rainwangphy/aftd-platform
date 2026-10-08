import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr

/-!
# Cslib.LTS.MTr.nil_eq

Topic: computability   Node: c0056ab31460

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.nil_eq`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

In any zero-steps multistep transition, the origin and the derivative are the same.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- In any zero-steps multistep transition, the origin and the derivative are the same. -/
@[grind .]
theorem Cslib.LTS.MTr.nil_eq (h : lts.MTr s1 [] s2) : s1 = s2 := by
  cases h
  rfl
