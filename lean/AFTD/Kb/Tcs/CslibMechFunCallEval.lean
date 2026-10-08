import AFTD.Prelude

/-!
# Cslib.Mech.FunCallEval

Topic: distributed   Node: e5d71734dd93

Provenance: formalization of a published result. Source: CSLib, `Cslib.Mech.FunCallEval`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/LocalComputation.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Type of (potentially nondeterministic) evaluation relations for local function calls at processes.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Type of (potentially nondeterministic) evaluation relations for local function calls at processes. -/
abbrev Cslib.Mech.FunCallEval FunId Val := (f : FunId) → (args : List Val) → Val → Prop
