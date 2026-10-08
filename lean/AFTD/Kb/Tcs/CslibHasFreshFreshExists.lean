import AFTD.Prelude
import AFTD.Kb.Tcs.CslibHasFresh

/-!
# Cslib.HasFresh.fresh_exists

Topic: algorithms   Node: b4a5aab770ff

Provenance: formalization of a published result. Source: CSLib, `Cslib.HasFresh.fresh_exists`. Lean proof by Fabrizio Montesi, Kenny Lau, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Data/HasFresh.lean (Copyright (c) 2025 Fabrizio Montesi. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An existential version of the `HasFresh` typeclass. This is useful for the sake of brevity in proofs.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
/-- An existential version of the `HasFresh` typeclass. This is useful for the sake of brevity in proofs. -/
theorem Cslib.HasFresh.fresh_exists {α : Type u} [HasFresh α] (s : Finset α) : ∃ a, a ∉ s :=
  ⟨fresh s, fresh_notMem s⟩
