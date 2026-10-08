import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoorof
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderDominantOfSubset
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.collision_door_valid

Topic: general_equilibrium   Node: 8b265e08de5e

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.collision_door_valid`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.collision_door_valid
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
open Classical in
variable (c : T → I) (σ : Finset T) (C : Finset I) in
variable {c σ C} in
omit [DecidableEq T] [Inhabited T] in
lemma IndexedLOrder.collision_door_valid [DecidableEq T] (σ : Finset T) (C : Finset I) (_ : T → I)
    (x : T) (h_cell : isCell σ C) (hx_in_σ : x ∈ σ) (h_card_eq : C.card = σ.card) :
    isDoorof (σ.erase x) C σ C := by
  apply isDoorof.idoor h_cell
  · constructor
    · exact Dominant_of_subset σ (σ.erase x) C (Finset.erase_subset x σ) h_cell
    · rw [h_card_eq]
      rw [Finset.card_erase_of_mem hx_in_σ]
      exact (Nat.sub_add_cancel (Finset.card_pos.mpr ⟨x, hx_in_σ⟩)).symm
  · exact Finset.notMem_erase x σ
  · exact Finset.insert_erase hx_in_σ
  · rfl

-- Lemma 7
