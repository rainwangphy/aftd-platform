import AFTD.Prelude
import AFTD.Kb.Tcs.SetReflOn
import AFTD.Kb.Tcs.RelationDom

/-!
# Set.LeftQuasiRefl

Topic: computability   Node: 93a588a329b9

Provenance: formalization of a published result. Source: CSLib, `Set.LeftQuasiRefl`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`LeftQuasiRefl r` is true when a relation `r` is reflexive on its domain.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- `LeftQuasiRefl r` is true when a relation `r` is reflexive on its domain. -/
abbrev Set.LeftQuasiRefl (r : α → α → Prop) := (dom r).ReflOn r
