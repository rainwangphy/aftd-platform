import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.UnlabelledTr

Topic: computability   Node: d3ee4074b812

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.UnlabelledTr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The unlabelled transition relation underlying an LTS.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- The unlabelled transition relation underlying an LTS. -/
def Cslib.LTS.UnlabelledTr (lts : LTS State Label) : State → State → Prop :=
  fun s1 s2 => ∃ μ, lts.Tr s1 μ s2
