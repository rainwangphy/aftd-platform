import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMini
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMSet
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMElement
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsMaximalInMSet
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMElementIsMaximal
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell

/-!
# IndexedLOrder.m_element_not_in_tau

Topic: general_equilibrium   Node: dbe5490d263e

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.m_element_not_in_tau`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.m_element_not_in_tau
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
omit [Inhabited T][DecidableEq T] in
lemma IndexedLOrder.m_element_not_in_tau [Fintype T] (τ : Finset T) (D : Finset I) (i a b : I)
    (h_door : IST.isDoor τ D) (h_nonempty : τ.Nonempty)
    (ha_mem : a ∈ D) (hb_mem : b ∈ D) (hab : a ≠ b)
    (h_eq_mini : mini h_nonempty a = mini h_nonempty b)
    (h_M_nonempty : (M_set τ D i h_nonempty).Nonempty)
    (h_i_is : i = a ∨ i = b) :
    m_element τ D i h_nonempty h_M_nonempty ∉ τ := by
  let m_i := m_element τ D i h_nonempty h_M_nonempty
  have h_max : is_maximal_in_M_set τ D i h_nonempty m_i :=
    m_element_is_maximal τ D i h_nonempty h_M_nonempty
  intro h_m_in_tau
  obtain ⟨k, hk_mem, hk_dom⟩ := h_door.1 m_i
  by_cases hk_eq_i : k = i
  · subst hk_eq_i
    have h_m_le_mini : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    have h_m_eq_mini : m_i = mini h_nonempty k := by
      letI := IST k
      have h_mini_le_m : mini h_nonempty k ≤[k] m_i := Finset.min'_le τ m_i h_m_in_tau
      exact le_antisymm h_m_le_mini h_mini_le_m
    have h_m_in_M : m_i ∈ M_set τ D k h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    cases h_i_is with
    | inl hi_eq_a =>
      subst hi_eq_a
      have h_mini_b_lt_m : mini h_nonempty b <[b] m_i := h_m_in_M b hb_mem hab.symm
      rw [h_m_eq_mini, h_eq_mini] at h_mini_b_lt_m
      letI := IST b
      exact lt_irrefl (mini h_nonempty b) h_mini_b_lt_m
    | inr hi_eq_b =>
      subst hi_eq_b
      have h_mini_a_lt_m : mini h_nonempty a <[a] m_i := h_m_in_M a ha_mem hab
      rw [h_m_eq_mini, ← h_eq_mini] at h_mini_a_lt_m
      letI := IST a
      exact lt_irrefl (mini h_nonempty a) h_mini_a_lt_m
  · have h_m_in_M : m_i ∈ M_set τ D i h_nonempty := h_max.1
    unfold M_set at h_m_in_M
    have h_mini_k_lt_m : mini h_nonempty k <[k] m_i := h_m_in_M k hk_mem hk_eq_i
    have h_m_le_mini_k : m_i ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) (by
      unfold mini
      exact @Finset.min'_mem _ (IST k) _ h_nonempty)
    letI := IST k
    exact not_le.mpr h_mini_k_lt_m h_m_le_mini_k
