import AFTD.Prelude

/-!
# Cslib.FinFun

Topic: algorithms   Node: 6666567cb024

Provenance: formalization of a published result. Source: CSLib, `Cslib.FinFun`. Lean proof by Fabrizio Montesi, Xueying Qin, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/FinFun/Basic.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `FinFun` is a function `fn` with a finite `support`. This is similar to `Finsupp` in Mathlib, but definitions are computable.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A `FinFun` is a function `fn` with a finite `support`. This is similar to `Finsupp` in Mathlib, but definitions are computable. -/
structure Cslib.FinFun (α β : Type*) [Zero β] where
  /-- The underlying function. -/
  fn : α → β
  /-- The finite support of the function. -/
  support : Finset α
  /-- Proof that `support` is the support of the underlying function. -/
  mem_support_fn {a : α} : a ∈ support ↔ fn a ≠ 0
