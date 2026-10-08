import AFTD.Prelude
import AFTD.Kb.Tcs.SetReflOn
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationOfCod
import AFTD.Kb.Tcs.RelationMemCod
import AFTD.Kb.Tcs.RelationCodEmpty
import AFTD.Kb.Tcs.RelationCodEqEmptyIff
import AFTD.Kb.Tcs.RelationCodInv
import AFTD.Kb.Tcs.RelationDomInv

/-!
# Set.ReflOn.of_cod

Topic: computability   Node: 37cc00955661

Provenance: formalization of a published result. Source: CSLib, `Set.ReflOn.of_cod`. Lean proof by Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Restriction.lean (Copyright (c) 2026 Chris Henson. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Set.ReflOn.of_cod
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
variable (r : α → α → Prop) (s : Set α) in
theorem Set.ReflOn.of_cod {r} : (cod r).ReflOn r → r a b → r b b | h, hab => h b (Relation.of_cod hab)
