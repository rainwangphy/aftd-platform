import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Deterministic

Topic: computability   Node: 7c093f009483

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Deterministic`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 adapted; compiled here.

An lts is deterministic if a state cannot reach different states with the same transition label.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An lts is deterministic if a state cannot reach different states with the same transition label. -/
@[grind]
class Cslib.LTS.Deterministic (lts : LTS State Label) where
  deterministic (s1 : State) (μ : Label) (s2 s3 : State) :
    lts.Tr s1 μ s2 → lts.Tr s1 μ s3 → s2 = s3
