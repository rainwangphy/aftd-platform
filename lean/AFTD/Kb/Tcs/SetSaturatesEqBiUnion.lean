import AFTD.Prelude
import AFTD.Kb.Tcs.SetSaturates
import AFTD.Kb.Tcs.SetSaturatesCompl

/-!
# Set.saturates_eq_biUnion

Topic: algorithms   Node: 006be0b7e257

Provenance: formalization of a published result. Source: CSLib, `Set.saturates_eq_biUnion`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Set/Saturation.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `f` is a cover and saturates `s`, then `s` is the union of all `f i` that intersects `s`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι α : Type*} in
variable {f : ι → Set α} {s : Set α} in
/-- If `f` is a cover and saturates `s`, then `s` is the union of all `f i` that intersects `s`. -/
theorem Set.saturates_eq_biUnion (hs : Saturates f s) (hc : ⋃ i, f i = univ) :
    s = ⋃ i ∈ {i | (f i ∩ s).Nonempty}, f i := by
  ext x
  simp only [mem_iUnion]
  constructor
  · intro h_x
    obtain ⟨i, _⟩ := mem_iUnion.mp <| univ_subset_iff.mpr hc <| mem_univ x
    use i, ⟨x, by grind⟩, by grind
  · rintro ⟨i, h_i, _⟩
    grind [hs i h_i]
