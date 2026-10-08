import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMini

/-!
# IndexedLOrder.M_set

Topic: general_equilibrium   Node: 3eca4aa6406d

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.M_set`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.M_set
-/

set_option quotPrecheck false
set_option hygiene false
local notation  lhs "<[" i "]" rhs => (IST i).lt lhs rhs
local notation  lhs "≤[" i "]" rhs => (IST i).le lhs rhs
set_option hygiene true

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open IndexedLOrder in
open Classical in
variable {T : Type*} [Inhabited T] in
variable {I : Type*} in
variable [IST : IndexedLOrder I T] in
set_option quotPrecheck false in
variable (σ : Finset T) (C : Finset I) in
variable [DecidableEq T] [DecidableEq I] in
def IndexedLOrder.M_set (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty) : Set T :=
  {y : T | ∀ k ∈ D, k ≠ i → mini h_nonempty k <[k] y}

-- Predicate for being the maximal element of M_i with respect to <_i
