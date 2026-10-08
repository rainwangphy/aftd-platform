import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.three_collision_card_bound

Topic: general_equilibrium   Node: e5ea80024355

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.three_collision_card_bound`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.three_collision_card_bound
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
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
omit [DecidableEq T] [Inhabited T] IST in
lemma IndexedLOrder.three_collision_card_bound [DecidableEq T] (σ : Finset T) (c : T → I)
    (a b z : T) (ha_in_σ : a ∈ σ) (hb_in_σ : b ∈ σ) (hz_in_σ : z ∈ σ)
    (hab_ne : a ≠ b) (haz_ne : a ≠ z) (hbz_ne : b ≠ z)
    (hc_eq : c a = c b) (hcz_eq : c b = c z) :
    σ.card ≥ (σ.image c).card + 2 := by
  let σ_rest := σ \ {a, b, z}
  have h_three_subset_sigma : {a, b, z} ⊆ σ := by
    intro w hw; simp at hw; rcases hw with (rfl | rfl | rfl);
    · exact ha_in_σ
    · exact hb_in_σ
    · exact hz_in_σ

  have h_partition : σ = {a, b, z} ∪ σ_rest :=
    (Finset.union_sdiff_of_subset h_three_subset_sigma).symm

  have h_disjoint : Disjoint ({a, b, z} : Finset T) σ_rest :=
    Finset.disjoint_sdiff

  have h_card_partition : σ.card = ({a, b, z} : Finset T).card + σ_rest.card := by
    rw [h_partition, Finset.card_union_of_disjoint h_disjoint]

  have h_triple_card : ({a, b, z} : Finset T).card = 3 := by
    rw [Finset.card_eq_three]
    exact ⟨a, b, z, hab_ne, haz_ne, hbz_ne, rfl⟩

  have h_image_bound : (σ.image c).card ≤ σ_rest.card + 1 := by
    have h_image_union : σ.image c = insert (c a) (σ_rest.image c) := by
      ext i; simp only [Finset.mem_image, Finset.mem_insert]
      constructor
      · rintro ⟨t, ht_in_σ, rfl⟩
        by_cases h_t_abz : t ∈ ({a, b, z} : Finset T)
        · simp at h_t_abz; rcases h_t_abz with (rfl | rfl | rfl)
          · left; rfl
          · left; exact hc_eq.symm
          · left; exact (hc_eq.trans hcz_eq).symm
        · right; use t; simp [σ_rest, ht_in_σ, h_t_abz]
      · rintro (rfl | ⟨t, ht_in_rest, rfl⟩)
        · use a
        · use t; exact ⟨(Finset.mem_sdiff.mp ht_in_rest).1, rfl⟩
    rw [h_image_union]
    linarith [Finset.card_insert_le (c a) (σ_rest.image c), Finset.card_image_le (f := c) (s := σ_rest)]

  calc σ.card
      = 3 + σ_rest.card           := by rw [h_card_partition, h_triple_card]
    _ = σ_rest.card + 3           := by ring
    _ = (σ_rest.card + 1) + 2     := by ring
    _ ≥ (σ.image c).card + 2      := by linarith
