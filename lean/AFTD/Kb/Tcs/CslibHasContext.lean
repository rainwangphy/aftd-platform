import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasHContext

/-!
# Cslib.HasContext

Topic: computability   Node: 4cece555b864

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasContext`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Syntax/Context.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Class for types (`α`) that have a canonical notion of homogeneous single-hole contexts (`Context`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Class for types (`α`) that have a canonical notion of homogeneous single-hole contexts (`Context`). -/
abbrev Cslib.HasContext (α : Type*) := HasHContext α α
