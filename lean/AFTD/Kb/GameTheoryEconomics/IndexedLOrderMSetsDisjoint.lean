import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMini
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderMSet
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell

/-!
# IndexedLOrder.M_sets_disjoint

Topic: general_equilibrium   Node: 2f5a9c4d7093

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.M_sets_disjoint`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.M_sets_disjoint
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
lemma IndexedLOrder.M_sets_disjoint [Fintype T] (τ : Finset T) (D : Finset I) (a b : I)
    (h_nonempty : τ.Nonempty) (h_door : IST.isDoor τ D)
    (ha : a ∈ D) (hb : b ∈ D) (hab : a ≠ b)
    (h_eq : mini h_nonempty a = mini h_nonempty b) :
    M_set τ D a h_nonempty ∩ M_set τ D b h_nonempty = ∅ := by
  ext y
  simp only [Set.mem_inter_iff, Set.mem_empty_iff_false]
  constructor
  · intro ⟨h_in_a, h_in_b⟩
    unfold M_set at h_in_a h_in_b
    have h_b_ne_a : b ≠ a := hab.symm
    have h_mini_b_lt_y : mini h_nonempty b <[b] y := h_in_a b hb h_b_ne_a
    have h_mini_a_lt_y : mini h_nonempty a <[a] y := h_in_b a ha hab
    rw [h_eq] at h_mini_a_lt_y
    obtain ⟨k, hk_in_D, hk_dom⟩ := h_door.1 y
    have h_mini_b_mem : mini h_nonempty b ∈ τ := by
      unfold mini
      exact @Finset.min'_mem _ (IST b) _ h_nonempty
    have h_y_le_mini_b : y ≤[k] mini h_nonempty b := hk_dom (mini h_nonempty b) h_mini_b_mem
    by_cases hk_eq_a : k = a
    · subst hk_eq_a
      letI := IST k
      exact not_le.mpr h_mini_a_lt_y h_y_le_mini_b
    · by_cases hk_eq_b : k = b
      · subst hk_eq_b
        letI := IST k
        exact not_le.mpr h_mini_b_lt_y h_y_le_mini_b
      · have h_mini_k_lt_y : mini h_nonempty k <[k] y := h_in_a k hk_in_D hk_eq_a
        have h_mini_k_mem : mini h_nonempty k ∈ τ := by
          unfold mini
          exact @Finset.min'_mem _ (IST k) _ h_nonempty
        have h_y_le_mini_k : y ≤[k] mini h_nonempty k := hk_dom (mini h_nonempty k) h_mini_k_mem
        letI := IST k
        exact not_le.mpr h_mini_k_lt_y h_y_le_mini_k
  · intro h
    exact False.elim h
