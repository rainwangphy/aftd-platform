import AFTD.Prelude

/-!
# Fin.succSuccAbove

Topic: special_relativity   Node: 4348086b1712

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The embedding of `Fin n` into `Fin (n + 1 + 1)` which leaves a hole at `i` and `j`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
/-- The embedding of `Fin n` into `Fin (n + 1 + 1)` which leaves a hole at `i` and `j`. -/
def Fin.succSuccAbove (i j : Fin (n + 1 + 1)) (m : Fin n) : Fin (n + 1 + 1) :=
  if m.1 < i.1 ∧ m.1 < j.1 then
    ⟨m, by omega⟩
  else if m.1 + 1 < i.1 ∧ j.1 ≤ m.1 then
    ⟨m + 1, by omega⟩
  else if i.1 ≤ m.1 ∧ m.1 + 1 < j.1 then
    ⟨m + 1, by omega⟩
  else
    ⟨m + 2, by omega⟩
