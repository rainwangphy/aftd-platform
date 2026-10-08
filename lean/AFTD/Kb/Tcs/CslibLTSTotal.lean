import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS

/-!
# Cslib.LTS.Total

Topic: computability   Node: 7c2d5fb0de0e

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Total`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Total.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An LTS is total iff every state has a `μ`-derivative for every label `μ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib in
variable {State Label : Type*} {lts : LTS State Label} in
/-- An LTS is total iff every state has a `μ`-derivative for every label `μ`. -/
class Cslib.LTS.Total (lts : LTS State Label) where
  /-- The condition of being total. -/
  total s μ : ∃ s', lts.Tr s μ s'
