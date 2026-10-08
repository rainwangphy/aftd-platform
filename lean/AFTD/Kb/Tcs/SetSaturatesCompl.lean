import AFTD.Prelude
import AFTD.Kb.Tcs.SetSaturates

/-!
# Set.saturates_compl

Topic: algorithms   Node: 16237631d8a6

Provenance: formalization of a published result. Source: CSLib, `Set.saturates_compl`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Set/Saturation.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

If `f` saturates `s`, then `f` saturates its complement `sᶜ` as well.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι α : Type*} in
variable {f : ι → Set α} {s : Set α} in
/-- If `f` saturates `s`, then `f` saturates its complement `sᶜ` as well. -/
@[simp, scoped grind .]
theorem Set.saturates_compl (hs : Saturates f s) : Saturates f sᶜ := by
  rintro i ⟨_, _⟩ y _ _
  have : (f i ∩ s).Nonempty := ⟨y, by grind⟩
  grind [Saturates]
