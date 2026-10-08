import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IndexedLOrder
import AFTD.Kb.GameTheoryEconomics.InstFunLikeIndexedLOrderLinearOrder

/-!
# IndexedLOrder.image_erase_eq_erase_image_of_unique

Topic: general_equilibrium   Node: 03faec41aee0

Provenance: formalization of a published result. Source: EconCSLib, `IndexedLOrder.image_erase_eq_erase_image_of_unique`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/Math/FixedPoint/Scarf.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

IndexedLOrder.image_erase_eq_erase_image_of_unique
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
variable {T I : Type*} [DecidableEq T] [DecidableEq I] in
lemma IndexedLOrder.image_erase_eq_erase_image_of_unique
  (σ : Finset T) (c : T → I) {z : T}
  (_ : z ∈ σ)
  (uniq : ∀ ⦃w⦄, w ∈ σ → c w = c z → w = z) :
  (σ.erase z).image c = (σ.image c).erase (c z) := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨w, hw_in_erase, rfl⟩
    rcases Finset.mem_erase.mp hw_in_erase with ⟨hw_ne_z, hw_in_σ⟩
    have h_ne_color : c w ≠ c z := by
      intro h_eq
      have := uniq hw_in_σ h_eq
      exact hw_ne_z this
    exact Finset.mem_erase.mpr ⟨h_ne_color, Finset.mem_image.mpr ⟨w, hw_in_σ, rfl⟩⟩
  · intro hi
    rcases Finset.mem_erase.mp hi with ⟨h_i_ne, hi_img⟩
    rcases Finset.mem_image.mp hi_img with ⟨w, hw_in_σ, rfl⟩
    have hw_ne_z : w ≠ z := by
      intro h_eq
      apply h_i_ne
      simp [h_eq]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hw_ne_z, hw_in_σ⟩, rfl⟩
