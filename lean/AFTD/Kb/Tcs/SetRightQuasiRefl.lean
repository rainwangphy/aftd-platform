import AFTD.Prelude
import AFTD.Kb.Tcs.SetReflOn
import AFTD.Kb.Tcs.RelationCod

/-!
# Set.RightQuasiRefl

Topic: computability   Node: 93ae02b61413

Provenance: formalization of a published result. Source: CSLib, `Set.RightQuasiRefl`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`RightQuasiRefl r` is true when a relation `r` is reflexive on its codomain.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- `RightQuasiRefl r` is true when a relation `r` is reflexive on its codomain. -/
abbrev Set.RightQuasiRefl (r : α → α → Prop) := (cod r).ReflOn r
