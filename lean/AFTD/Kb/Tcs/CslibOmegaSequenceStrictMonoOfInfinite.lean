import AFTD.Prelude
import AFTD.Kb.Tcs.CslibOmegaSequence

/-!
# Cslib.ωSequence.strictMono_of_infinite

Topic: algorithms   Node: 48def43f2353

Provenance: formalization of a published result. Source: CSLib, `Cslib.ωSequence.strictMono_of_infinite`. Lean proof by Ching-Tsun Chou, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/OmegaSequence/InfOcc.lean (Copyright (c) 2025 Ching-Tsun Chou. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Every infinite subset of ℕ is the range of a strictly monotonic function from ℕ to ℕ.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Function Set Filter in
universe u v w in
variable {α : Type u} {β : Type v} {δ : Type w} in
open Nat in
/-- Every infinite subset of ℕ is the range of a strictly monotonic function from ℕ to ℕ. -/
theorem Cslib.ωSequence.strictMono_of_infinite {ns : Set ℕ} (h : ns.Infinite) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ range f = ns :=
  ⟨nth (· ∈ ns), nth_strictMono h, range_nth_of_infinite h⟩
