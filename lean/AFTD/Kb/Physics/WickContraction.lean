import AFTD.Prelude
import AFTD.Kb.Physics.FieldSpecification

/-!
# WickContraction

Topic: quantum_field_theory   Node: 236598bde751

Provenance: formalization of a published result. Source: Physlib, `WickContraction`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QFT/PerturbationTheory/WickContraction/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a natural number `n`, which will correspond to the number of fields needing contracting, a Wick contraction is a finite set of pairs of `Fin n` (numbers `0`, ..., `n-1`), such that no element of `Fin n` occurs in more than one pair. The pairs are the positions of fields we 'contract' together.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {𝓕 : FieldSpecification} in
/-- Given a natural number `n`, which will correspond to the number of fields needing contracting, a Wick contraction is a finite set of pairs of `Fin n` (numbers `0`, ..., `n-1`), such that no element of `Fin n` occurs in more than one pair. The pairs are the positions of fields we 'contract' together. -/
def WickContraction (n : ℕ) : Type :=
  {f : Finset ((Finset (Fin n))) // (∀ a ∈ f, a.card = 2) ∧
    (∀ a ∈ f, ∀ b ∈ f, a = b ∨ Disjoint a b)}
