import AFTD.Prelude
import AFTD.Kb.Tcs.CslibSKI

/-!
# Cslib.SKI.Polynomial

Topic: computability   Node: 77ad3e6e30fa

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI.Polynomial`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Basic.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A polynomial is an SKI terms with free variables.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Relation in
/-- A polynomial is an SKI terms with free variables. -/
protected inductive Cslib.SKI.Polynomial (n : Nat) : Type where
  | term : SKI → SKI.Polynomial n
  | var : Fin n → SKI.Polynomial n
  | app : SKI.Polynomial n → SKI.Polynomial n → SKI.Polynomial n
