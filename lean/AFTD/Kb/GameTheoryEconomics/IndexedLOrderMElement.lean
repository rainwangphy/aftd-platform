import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMSet
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.m_element

Topic: general_equilibrium   Node: 86488bb00ae4

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.m_element`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.m_element
-/

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
noncomputable def IndexedLOrder.m_element [Fintype T] (τ : Finset T) (D : Finset I) (i : I) (h_nonempty : τ.Nonempty)
    (h : (M_set τ D i h_nonempty).Nonempty) : T :=
  @Finset.max' _ (IST i) (M_set τ D i h_nonempty).toFinset (Set.toFinset_nonempty.mpr h)

-- Theorem: m_element is indeed the maximal element
