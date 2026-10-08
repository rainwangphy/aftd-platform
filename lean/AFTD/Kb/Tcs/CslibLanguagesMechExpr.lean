import AFTD.Prelude

/-!
# Cslib.Languages.Mech.Expr

Topic: distributed   Node: 0217baef565a

Provenance: formalization of a published result. Source: CSLib, `Cslib.Languages.Mech.Expr`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/Mech/Choreography/Basic.lean (Copyright (c) 2026 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Expressions for local computation.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- Expressions for local computation. -/
inductive Cslib.Languages.Mech.Expr (Var Val FunId : Type*) where
  /-- Read variable `x`. -/
  | var (x : Var)
  /-- Value `v`. -/
  | val (v : Val)
  /-- Call function `f` with arguments `args`. -/
  | call (f : FunId) (args : List (Expr Var Val FunId))
