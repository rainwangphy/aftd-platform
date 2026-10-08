import AFTD.Prelude

/-!
# Cslib.Algorithms.Lean.TimeM

Topic: algorithms   Node: d7afe9a0d7d8

Provenance: formalization of a published result. Source: CSLib, `Cslib.Algorithms.Lean.TimeM`. Lean proof by Sorrachai Yingchareonthawornhcai, Eric Wieser, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Algorithms/Lean/TimeM.lean (Copyright (c) 2025 Sorrachai Yingchareonthawornhcai. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A monad for tracking time complexity of computations. `TimeM T α` represents a computation that returns a value of type `α` and accumulates a time cost (represented as a type `T`, typically `ℕ`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A monad for tracking time complexity of computations. `TimeM T α` represents a computation that returns a value of type `α` and accumulates a time cost (represented as a type `T`, typically `ℕ`). -/
@[ext]
structure Cslib.Algorithms.Lean.TimeM (T : Type*) (α : Type*) where
  /-- The return value of the computation -/
  ret : α
  /-- The accumulated time cost of the computation -/
  time : T
