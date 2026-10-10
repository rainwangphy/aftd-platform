import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveEqSuccAboveSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveEqIffEq
import AFTD.Kb.Physics.FinSuccSuccAboveLeqIffLeq
import AFTD.Kb.Physics.FinSuccSuccAboveLtIffLt
import AFTD.Kb.Physics.FinSuccSuccAboveMonotone

/-!
# Fin.succSuccAbove_range

Topic: special_relativity   Node: fb5cd316d666

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_range`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_range
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
@[simp]
lemma Fin.succSuccAbove_range {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    Set.range (succSuccAbove i j) = {i, j}ᶜ := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · simp_all
  rw [succSuccAbove_eq_succAbove_succAbove, Set.range_comp, Fin.range_succAbove]
  ext a
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_image]
  apply Iff.intro
  · intro h
    obtain ⟨b, h1, rfl⟩ := h
    simpa using h1
  · intro h
    simp at h
    rcases Fin.eq_self_or_eq_succAbove i a with rfl | ⟨a, rfl⟩
    · simp_all
    use a
    simp_all
