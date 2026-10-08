import AFTD.Prelude

/-!
# Cslib.LambdaCalculus.Named.Term

Topic: computability   Node: 22825597908c

Provenance: formalization of a published result. Source: CSLib, `Cslib.LambdaCalculus.Named.Term`. Lean proof by Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/LambdaCalculus/Named/Untyped/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Syntax of terms.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {Var : Type u} in
/-- Syntax of terms. -/
inductive Cslib.LambdaCalculus.Named.Term (Var : Type u) : Type u where
  | var (x : Var)
  | abs (x : Var) (m : Term Var)
  | app (m n : Term Var)
deriving DecidableEq
