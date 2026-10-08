import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSMTr
import AFTD.Kb.Tcs.CslibLTSMTrNilIff
import AFTD.Kb.Tcs.CslibLTSMTrSingletonIff

/-!
# Cslib.LTS.BoundedUpTo

Topic: computability   Node: cf2c1f637c68

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.BoundedUpTo`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An LTS is bounded up to `n` if every finite execution has length strictly less than `n`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An LTS is bounded up to `n` if every finite execution has length strictly less than `n`. -/
def Cslib.LTS.BoundedUpTo (lts : LTS State Label) (n : ℕ) : Prop :=
  ∀ s1 μs s2, lts.MTr s1 μs s2 → μs.length < n
