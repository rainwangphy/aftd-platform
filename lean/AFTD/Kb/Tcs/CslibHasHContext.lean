import AFTD.Prelude

/-!
# Cslib.HasHContext

Topic: computability   Node: e4760250c826

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasHContext`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Context.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Class for types with a canonical notion of heterogeneous single-hole contexts.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Class for types with a canonical notion of heterogeneous single-hole contexts. -/
class Cslib.HasHContext (α β : Type*) where
  /-- The type of contexts. -/
  {Context : Type*}
  /-- Replaces the hole in the context with a value, resulting in a new value. -/
  fill (c : Context) (b : β) : α
