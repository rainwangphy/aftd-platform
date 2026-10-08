import AFTD.Prelude

/-!
# Relation.LocallyConfluent

Topic: computability   Node: 94125925db28

Provenance: formalization of a published result. Source: CSLib, `Relation.LocallyConfluent`. Lean proof by Fabrizio Montesi, Thomas Waring, Chris Henson, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Relation/Defs.lean (Copyright (c) 2025 Fabrizio Montesi and Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A relation is locally confluent when all reductions with a common origin are multi-joinable
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A relation is locally confluent when all reductions with a common origin are multi-joinable -/
abbrev Relation.LocallyConfluent (r : α → α → Prop) :=
  ∀ {a b c : α}, r a b → r a c → Join (ReflTransGen r) b c
