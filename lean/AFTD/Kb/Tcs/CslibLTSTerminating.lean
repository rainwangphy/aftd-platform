import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.RelationTerminating
import AFTD.Kb.Tcs.CslibLTSUnlabelledTr

/-!
# Cslib.LTS.Terminating

Topic: computability   Node: 2d9d3497a086

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Terminating`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An LTS is terminating if its underlying unlabelled transition relation is terminating, equivalently if it admits no infinite execution.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Cslib Cslib.LTS in
universe u v in
variable {State : Type u} {Label : Type v} (lts : LTS State Label) in
/-- An LTS is terminating if its underlying unlabelled transition relation is terminating, equivalently if it admits no infinite execution. -/
class Cslib.LTS.Terminating (lts : LTS State Label) where
  terminating : Relation.Terminating lts.UnlabelledTr
