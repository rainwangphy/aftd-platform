import AFTD.Prelude
import AFTD.Kb.Tcs.RelationDom
import AFTD.Kb.Tcs.RelationCod
import AFTD.Kb.Tcs.RelationMemDom
import AFTD.Kb.Tcs.RelationMemCod
import AFTD.Kb.Tcs.RelationDomEmpty
import AFTD.Kb.Tcs.RelationCodEmpty
import AFTD.Kb.Tcs.RelationDomEqEmptyIff
import AFTD.Kb.Tcs.RelationCodEqEmptyIff
import AFTD.Kb.Tcs.RelationCodInv

/-!
# Relation.dom_inv

Topic: computability   Node: 45481bd4ce66

Provenance: formalization of a published result. Source: CSLib, `Relation.dom_inv`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Domain.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Relation.dom_inv
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {β : Type*} {r : α → β → Prop} in
@[simp]
lemma Relation.dom_inv : dom (fun a b => r b a) = cod r := rfl
