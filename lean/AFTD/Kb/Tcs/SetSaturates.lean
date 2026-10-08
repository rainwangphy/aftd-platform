import AFTD.Prelude

/-!
# Set.Saturates

Topic: algorithms   Node: da575aeaa3de

Provenance: formalization of a published result. Source: CSLib, `Set.Saturates`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/Set/Saturation.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`f : ι → Set α` saturates `s : Set α` iff `f i` is a subset of `s` whenever `f i` and `s` has any intersection at all.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι α : Type*} in
/-- `f : ι → Set α` saturates `s : Set α` iff `f i` is a subset of `s` whenever `f i` and `s` has any intersection at all. -/
def Set.Saturates (f : ι → Set α) (s : Set α) : Prop :=
  ∀ i : ι, (f i ∩ s).Nonempty → f i ⊆ s
