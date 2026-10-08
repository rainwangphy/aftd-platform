import AFTD.Prelude

/-!
# Cslib.infinite_pigeonhole_principle

Topic: combinatorics   Node: 5afd3a2b5d01

Provenance: formalization of a published result. Source: CSLib, `Cslib.infinite_pigeonhole_principle`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Combinatorics/InfiniteGraphRamsey.lean (Copyright (c) 2026 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An infinite pigeonhole principle.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set in
/-- An infinite pigeonhole principle. -/
theorem Cslib.infinite_pigeonhole_principle {X Y : Type*} [Finite Y] (f : X → Y) {s : Set X}
    (h_inf : s.Infinite) : ∃ y, ∃ t, t.Infinite ∧ t ⊆ s ∧ ∀ x ∈ t, f x = y := by
  have := h_inf.to_subtype
  obtain ⟨y, h_inf'⟩ := Finite.exists_infinite_fiber (s.domRestrict f)
  have h_inf_iff := Equiv.infinite_iff <|
    Equiv.subtypeSubtypeEquivSubtypeInter (· ∈ s) (fun x ↦ f x = y)
  use y, {x | x ∈ s ∧ f x = y}, infinite_coe_iff.mp <| h_inf_iff.mp h_inf'
  grind
