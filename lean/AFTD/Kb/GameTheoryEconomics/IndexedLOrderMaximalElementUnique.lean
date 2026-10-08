import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMSet
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsMaximalInMSet
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMElement
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMElementIsMaximal
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.maximal_element_unique

Topic: general_equilibrium   Node: 00a1b6a3f09b

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.maximal_element_unique`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.maximal_element_unique
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
omit [Inhabited T] [DecidableEq T] [DecidableEq I] in
lemma IndexedLOrder.maximal_element_unique [Fintype T] (τ : Finset T) (D : Finset I) (i : I)
    (h_nonempty : τ.Nonempty) (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (x : T) (h_x_max : is_maximal_in_M_set τ D i h_nonempty x) :
    x = m_element τ D i h_nonempty h_M_nonempty := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_mi_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  letI := IST i
  have h_x_in_M : x ∈ M_set τ D i h_nonempty := h_x_max.1
  have h_mi_in_M : m_i ∈ M_set τ D i h_nonempty := h_mi_max.1
  have h_x_le_mi : x ≤[i] m_i := h_mi_max.2 x h_x_in_M
  have h_mi_le_x : m_i ≤[i] x := h_x_max.2 m_i h_mi_in_M
  exact le_antisymm h_x_le_mi h_mi_le_x
