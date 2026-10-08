import AFTD.Prelude

/-!
# Cslib.SKI

Topic: computability   Node: 9c400b399bd8

Provenance: formalization of a published result. Source: CSLib, `Cslib.SKI`. Lean proof by Thomas Waring, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Languages/CombinatoryLogic/Defs.lean (Copyright (c) 2025 Thomas Waring. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An SKI expression is built from the primitive combinators `S`, `K` and `I`, and application.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- An SKI expression is built from the primitive combinators `S`, `K` and `I`, and application. -/
inductive Cslib.SKI where
  /-- `S`-combinator, with semantics $λxyz.xz(yz)$ -/
  | S
  /-- `K`-combinator, with semantics $λxy.x$ -/
  | K
  /-- `I`-combinator, with semantics $λx.x$ -/
  | I
  /-- Application $x y ↦ xy$ -/
  | app : SKI → SKI → SKI
deriving Repr, DecidableEq
