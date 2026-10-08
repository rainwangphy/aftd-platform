import AFTD.Prelude

/-!
# Cslib.ωSequence

Topic: algorithms   Node: 5a964fdbf244

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence`. Lean proof by Ching-Tsun Chou, Fabrizio Montesi, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/Defs.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `ωSequence α` is an infinite sequence of elements of `α`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- An `ωSequence α` is an infinite sequence of elements of `α`. -/
structure Cslib.ωSequence (α : Type u) where
  /-- The function that defines this infinite sequence. -/
  get : ℕ → α
