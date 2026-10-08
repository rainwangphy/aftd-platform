import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilEq

/-!
# Cslib.LTS.MTr.nil_iff

Topic: computability   Node: 28f2115cf520

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.MTr.nil_iff`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Cslib.LTS.MTr.nil_iff
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
@[simp] theorem Cslib.LTS.MTr.nil_iff (s1 s2 : State) : lts.MTr s1 [] s2 ↔ s1 = s2 :=
  ⟨nil_eq lts, fun h => h ▸ MTr.refl⟩
