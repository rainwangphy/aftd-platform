import AFTD.Prelude
import AFTD.Kb.Tcs.SetReflOn
import AFTD.Kb.Tcs.RelationDom
import AFTD.Kb.Tcs.RelationOfDom
import AFTD.Kb.Tcs.RelationMemDom
import AFTD.Kb.Tcs.RelationDomEmpty
import AFTD.Kb.Tcs.RelationDomEqEmptyIff
import AFTD.Kb.Tcs.RelationCodInv
import AFTD.Kb.Tcs.RelationDomInv

/-!
# Set.ReflOn.of_dom

Topic: computability   Node: b605e06848da

Provenance: formalization of a published result. Source: CSLib, `Set.ReflOn.of_dom`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Restriction.lean (Copyright (c) 2026 Chris Henson. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Set.ReflOn.of_dom
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
variable (r : α → α → Prop) (s : Set α) in
theorem Set.ReflOn.of_dom {r} : (dom r).ReflOn r → r a b → r a a | h, hab => h a (Relation.of_dom hab)
