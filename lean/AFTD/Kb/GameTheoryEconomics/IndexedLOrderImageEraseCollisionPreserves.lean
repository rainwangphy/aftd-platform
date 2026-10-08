import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.image_erase_collision_preserves

Topic: general_equilibrium   Node: 460d51981ea2

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.image_erase_collision_preserves`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.image_erase_collision_preserves
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
lemma IndexedLOrder.image_erase_collision_preserves [DecidableEq T] (σ : Finset T) (c : T → I)
    (x y : T) (hx_in_σ : x ∈ σ) (hy_in_σ : y ∈ σ) (hxy_ne : x ≠ y) (hcxy_eq : c x = c y) :
    (σ.erase x).image c = σ.image c ∧ (σ.erase y).image c = σ.image c := by
  constructor
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_σ : w ∈ σ := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_σ, hw_eq⟩
    · intro ⟨w, hw_in_σ, hw_eq⟩
      by_cases h : w = x
      · subst h
        use y
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne.symm, hy_in_σ⟩
        · rw [←hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_σ⟩, hw_eq⟩
  · ext z
    simp only [Finset.mem_image]
    constructor
    · intro ⟨w, hw_in_erased, hw_eq⟩
      have hw_in_σ : w ∈ σ := by
        rw [Finset.mem_erase] at hw_in_erased
        exact hw_in_erased.2
      exact ⟨w, hw_in_σ, hw_eq⟩
    · intro ⟨w, hw_in_σ, hw_eq⟩
      by_cases h : w = y
      · subst h
        use x
        constructor
        · rw [Finset.mem_erase]
          exact ⟨hxy_ne, hx_in_σ⟩
        · rw [hcxy_eq, hw_eq]
      · use w
        exact ⟨Finset.mem_erase.mpr ⟨h, hw_in_σ⟩, hw_eq⟩
