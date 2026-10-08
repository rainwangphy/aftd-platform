import AFTD.Prelude

/-!
# Cslib.HasTau

Topic: computability   Node: 243bb05e2711

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasTau`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/HasTau.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A type of transition labels that includes a special 'internal' transition `τ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- A type of transition labels that includes a special 'internal' transition `τ`. -/
class Cslib.HasTau (Label : Type v) where
  /-- The internal transition label, also known as τ. -/
  τ : Label
