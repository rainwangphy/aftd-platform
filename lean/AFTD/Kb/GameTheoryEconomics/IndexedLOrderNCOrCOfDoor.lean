import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsTypedNC
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoorof
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsColorful
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsCell
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsDoor
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsRoom
import AFTD.Kb.GameTheoryEconomics.IndexedLOrderIsRoomOfDoor
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.NC_or_C_of_door

Topic: general_equilibrium   Node: d96ead58010a

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.NC_or_C_of_door`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.NC_or_C_of_door
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
omit [Inhabited T] in
lemma IndexedLOrder.NC_or_C_of_door (h1 : isTypedNC c i τ D) (h2 : isDoorof τ D σ C) : isTypedNC c i σ C ∨ isColorful c σ C := by
  unfold isTypedNC at h1 ⊢
  unfold isColorful
  have h1_cell := h1.left
  have h1_eq := h1.right

  have h_sigma_cell : isCell σ C := by
    cases h2 with
    | idoor h0 _ _ _ _ _ => exact h0
    | odoor h0 _ _ _ _ _ => exact h0

  have step1_subset : C \ (σ.image c) ⊆ D \ (τ.image c) := by
    intro y hy
    simp only [Finset.mem_sdiff] at hy ⊢
    obtain ⟨y_in_C, y_notin_img_sigma⟩ := hy
    constructor
    · cases h2
      · rename_i h_D_eq; rw [h_D_eq]; exact y_in_C
      · rename_i h_D_eq; rw [h_D_eq]; exact Finset.mem_insert_of_mem y_in_C
    · cases h2 with
      | idoor h0 hdoor x h_x_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq, Finset.image_insert] at y_notin_img_sigma
        simp only [Finset.mem_insert, not_or] at y_notin_img_sigma
        exact y_notin_img_sigma.2
      | odoor h0 hdoor j h_j_notin h_sigma_eq h_D_eq =>
        rw [← h_sigma_eq] at y_notin_img_sigma
        exact y_notin_img_sigma

  have step2_D_card : (D \ (τ.image c)).card = 1 := by
    have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
      rw [h1_eq]
    rw [D_sdiff_eq_i, Finset.card_singleton]

  have step3_C_card_le : (C \ σ.image c).card ≤ 1 := by
    rw [← step2_D_card]
    exact Finset.card_le_card step1_subset

  by_cases h : (C \ σ.image c).card = 0
  · right
    constructor
    · exact h_sigma_cell
    · have h_C_subset_img : C ⊆ σ.image c := by
        rw [Finset.subset_iff]
        intro x hx
        by_contra hxn
        have : x ∈ C \ σ.image c := by simp [hx, hxn]
        have : (C \ σ.image c).Nonempty := ⟨x, this⟩
        have : 0 < (C \ σ.image c).card := Finset.card_pos.2 this
        linarith [h]

      have h_room: isRoom σ C := isRoom_of_Door h2
      have h_card_eq : C.card = σ.card := h_room.2
      have h_img_le_C_card : (σ.image c).card ≤ C.card := by
        calc (σ.image c).card
          ≤ σ.card := Finset.card_image_le
          _ = C.card := h_card_eq.symm
      exact (Finset.eq_of_subset_of_card_le h_C_subset_img h_img_le_C_card).symm

  · left
    constructor
    · exact h_sigma_cell
    · have h_card_one : (C \ σ.image c).card = 1 := by omega

      have h_subset_singleton : C \ σ.image c ⊆ {i} := by
        have D_sdiff_eq_i : D \ (τ.image c) = {i} := by
          rw [h1_eq]
        rw [← D_sdiff_eq_i]
        exact step1_subset

      have C_sdiff_eq_i : C \ σ.image c = {i} :=
        Finset.eq_of_subset_of_card_le h_subset_singleton (by rw [h_card_one, Finset.card_singleton])

      have h_i_notin_img : i ∉ σ.image c := by
        have h_i_in_sdiff : i ∈ C \ σ.image c := by rw [C_sdiff_eq_i]; simp
        exact (Finset.mem_sdiff.mp h_i_in_sdiff).2

      exact C_sdiff_eq_i
