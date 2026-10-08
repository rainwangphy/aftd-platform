import AFTD.Prelude

/-!
# Cslib.ωSequence.frequently_iff_strictMono

Topic: algorithms   Node: 361fab75eedc

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.frequently_iff_strictMono`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/InfOcc.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An alternative characterization of "infinitely often".
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set Filter in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
/-- An alternative characterization of "infinitely often". -/
theorem Cslib.ωSequence.frequently_iff_strictMono {p : ℕ → Prop} :
    (∃ᶠ n in atTop, p n) ↔ ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ m, p (f m) := by
  constructor
  · intro h
    exact extraction_of_frequently_atTop h
  · rintro ⟨f, h_mono, h_p⟩
    rw [Nat.frequently_atTop_iff_infinite]
    have h_range : range f ⊆ {n | p n} := by grind
    grind [Infinite.mono, infinite_range_of_injective, StrictMono.injective]
