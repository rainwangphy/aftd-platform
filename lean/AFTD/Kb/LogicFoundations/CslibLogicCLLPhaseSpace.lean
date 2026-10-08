import AFTD.Prelude

/-!
# Cslib.Logic.CLL.PhaseSpace

Topic: proof_theory   Node: 75eb6ffab413

Provenance: formalization of a published result. Source: CSLib, `Cslib.Logic.CLL.PhaseSpace`. Lean proof by Tanner Duve, Bhavik Mehta, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Logics/LinearLogic/CLL/PhaseSemantics/Basic.lean (Copyright (c) 2025 Tanner Duve. All rights reserved, Apache-2.0); 1 adapted; compiled here.

A phase space is a commutative monoid M equipped with a distinguished subset ⊥. This forms the algebraic foundation for interpreting linear logic propositions.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
open scoped Pointwise in
open Set in
attribute [local grind _=_] Set.le_iff_subset in
/-- A phase space is a commutative monoid M equipped with a distinguished subset ⊥. This forms the algebraic foundation for interpreting linear logic propositions. -/
class Cslib.Logic.CLL.PhaseSpace (M : Type u) extends CommMonoid M where
  /-- The distinguished subset ⊥ used to define orthogonality -/
  bot : Set M
