import AFTD.Prelude

/-!
# PFunctor.FreeM

Topic: algorithms   Node: adc89985dd9d

Provenance: formalization of a published result. Source: CSLib, `PFunctor.FreeM`. Lean proof by Quang Dao, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/PFunctor/Free.lean (Copyright (c) 2026 Quang Dao. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The free monad on a polynomial functor. This extends `WType` with an extra `pure` constructor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v uA uB in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The free monad on a polynomial functor. This extends `WType` with an extra `pure` constructor. -/
inductive PFunctor.FreeM (P : PFunctor.{uA, uB}) : Type v → Type (max uA uB v)
  /-- A leaf node wrapping a pure value. -/ | protected pure {α} (a : α) : P.FreeM α
  /-- Invoke the operation `a : P.A` with continuation `cont : P.B a → P.FreeM α`. -/
  | liftBind {α} (a : P.A) (cont : P.B a → P.FreeM α) : P.FreeM α
deriving Inhabited
