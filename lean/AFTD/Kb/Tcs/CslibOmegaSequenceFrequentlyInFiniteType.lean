import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence
import AFTD.Kb.Tcs.CslibInstFunLikeOmegaSequenceNat
import AFTD.Kb.Tcs.CslibInstCoeForallNatOmegaSequence

/-!
# Cslib.ωSequence.frequently_in_finite_type

Topic: algorithms   Node: 6a60d4ccc8d7

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.frequently_in_finite_type`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/InfOcc.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

In a finite type, the elements of a set occurs infinitely often iff some element in the set occurs infinitely often.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set Filter in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- In a finite type, the elements of a set occurs infinitely often iff some element in the set occurs infinitely often. -/
theorem Cslib.ωSequence.frequently_in_finite_type [Finite α] {s : Set α} {xs : ωSequence α} :
    (∃ᶠ k in atTop, xs k ∈ s) ↔ ∃ x ∈ s, ∃ᶠ k in atTop, xs k = x := by
  constructor
  · intro h_inf
    rw [Nat.frequently_atTop_iff_infinite] at h_inf
    have : Infinite (xs ⁻¹' s) := h_inf.to_subtype
    let rf := Set.restrictPreimage s xs
    obtain ⟨⟨x, h_x⟩, h_inf'⟩ := Finite.exists_infinite_fiber rf
    rw [← Set.infinite_range_iff (Subtype.val_injective.comp Subtype.val_injective)] at h_inf'
    simp only [range, comp_apply, Subtype.exists, mem_preimage, mem_singleton_iff,
      restrictPreimage_mk, Subtype.mk.injEq, ← Nat.frequently_atTop_iff_infinite, rf] at h_inf'
    grind
  · rintro ⟨_, _, h_inf⟩
    apply Frequently.mono h_inf
    grind
