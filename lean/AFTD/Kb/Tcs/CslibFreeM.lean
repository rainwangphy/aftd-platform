import AFTD.Prelude

/-!
# Cslib.FreeM

Topic: computability   Node: f60cc56f8b5f

Provenance: formalization of a published result. Source: CSLib, `Cslib.FreeM`. Lean proof by Tanner Duve, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Control/Monad/Free.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Free monad over a type constructor `F`. A `FreeM F a` is a tree of operations from the type constructor `F`, with leaves of type `a`. It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for representing an operation from `F` followed by a continuation. This construction provides a free monad for any type constructor `F`, allowing for composable effect descriptions that can be interpreted later. Unlike the traditional free monad, this does not require `F` to be a functor.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option genInjectivity false in
set_option genSizeOfSpec false in
/-- The Free monad over a type constructor `F`. A `FreeM F a` is a tree of operations from the type constructor `F`, with leaves of type `a`. It has two constructors: `pure` for wrapping a value of type `a`, and `liftBind` for representing an operation from `F` followed by a continuation. This construction provides a free monad for any type constructor `F`, allowing for composable effect descriptions that can be interpreted later. Unlike the traditional free monad, this does not require `F` to be a functor. -/
inductive Cslib.FreeM.{u, v, w} (F : Type u → Type v) (α : Type w) where
  /-- The action that does nothing and returns `a`. -/
  | protected pure (a : α) : FreeM F α
  /-- Invoke the operation `op` with contuation `cont`.

  Note that Lean's inductive types prevent us splitting this into separate bind and lift
  constructors. -/
  | liftBind {ι : Type u} (op : F ι) (cont : ι → FreeM F α) : FreeM F α
