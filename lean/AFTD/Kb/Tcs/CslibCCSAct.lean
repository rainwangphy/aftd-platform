import AFTD.Prelude

/-!
# Cslib.CCS.Act

Topic: distributed   Node: 44657deff38b

Provenance: formalization of a published result. Source: CSLib, `Cslib.CCS.Act`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CCS/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Actions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
/-- Actions. -/
inductive Cslib.CCS.Act (Name : Type u) : Type u where
  | name (a : Name)
  | coname (a : Name)
  | τ
deriving DecidableEq
