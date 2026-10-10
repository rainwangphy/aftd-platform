import AFTD.Prelude

/-!
# Fin.append_castAdd_natAdd_eq_id

Topic: special_relativity   Node: dec2c724b322

Provenance: formalization of a published result. Source: Physlib, `Fin.append_castAdd_natAdd_eq_id`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Reindexing.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Splitting `Fin (m + n)` into its two blocks and reassembling them is the identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
/-- Splitting `Fin (m + n)` into its two blocks and reassembling them is the identity. -/
lemma Fin.append_castAdd_natAdd_eq_id {m n : ℕ} :
    Fin.append (Fin.castAdd n) (Fin.natAdd m) = (id : Fin (m + n) → Fin (m + n)) := by
  simpa using Fin.append_castAdd_natAdd (f := (id : Fin (m + n) → Fin (m + n)))
