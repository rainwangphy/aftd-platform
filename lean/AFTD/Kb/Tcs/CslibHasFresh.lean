import AFTD.Prelude

/-!
# Cslib.HasFresh

Topic: algorithms   Node: 8060c512938b

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasFresh`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 2 verbatim; compiled here.

A type `α` has a computable `fresh` function if it is always possible, for any finite set of `α`, to compute a fresh element not in the set.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- A type `α` has a computable `fresh` function if it is always possible, for any finite set of `α`, to compute a fresh element not in the set. -/
class Cslib.HasFresh (α : Type u) where
  /-- Given a finite set, returns an element not in the set. -/
  fresh : Finset α → α
  /-- Proof that `fresh` returns a fresh element for its input set. -/
  fresh_notMem (s : Finset α) : fresh s ∉ s

attribute [grind <=] Cslib.HasFresh.fresh_notMem
