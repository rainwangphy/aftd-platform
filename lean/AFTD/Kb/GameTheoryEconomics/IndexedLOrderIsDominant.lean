import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.isDominant

Topic: general_equilibrium   Node: a1b2401a89e0

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.isDominant`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`σ` is **dominant** with respect to `C`: for every `y : T` there exists `i ∈ C` such that every element of `σ` is ≥[i] y — i.e., `σ` contains, in the order at `i`, a minimum that dominates `y`. This is the key structural invariant of Scarf's lemma. It generalises the notion that a simplex vertex set "covers" a given point in its convex hull.
-/

set_option quotPrecheck false
set_option hygiene false
local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs
set_option hygiene true

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Classical in
variable {T : Type*} [Inhabited T] in
variable {I : Type*} in
variable [IST : IndexedLOrder I T] in
set_option quotPrecheck false in
variable (σ : Finset T) (C : Finset I) in
/-- `σ` is **dominant** with respect to `C`: for every `y : T` there exists `i ∈ C` such that every element of `σ` is ≥[i] y — i.e., `σ` contains, in the order at `i`, a minimum that dominates `y`. This is the key structural invariant of Scarf's lemma. It generalises the notion that a simplex vertex set "covers" a given point in its convex hull. -/
def IndexedLOrder.isDominant :=
  ∀ y, ∃ i ∈ C, ∀ x ∈ σ,  y ≤[i] x
