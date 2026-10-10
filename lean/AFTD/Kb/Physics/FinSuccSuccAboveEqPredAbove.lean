import AFTD.Prelude
import AFTD.Kb.Physics.FinSuccSuccAbove
import AFTD.Kb.Physics.FinSuccSuccAboveEqSuccAboveSuccAbove

/-!
# Fin.succSuccAbove_eq_predAbove

Topic: special_relativity   Node: 090369d2aafd

Provenance: formalization of a published result. Source: Physlib, `Fin.succSuccAbove_eq_predAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/Contraction/SuccSuccAbove.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Fin.succSuccAbove_eq_predAbove
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Fin in
variable {n : ℕ} {c : Fin (n + 1 + 1) → C} in
lemma Fin.succSuccAbove_eq_predAbove {i j : Fin (n + 1 + 1)} (hij : i ≠ j) :
    succSuccAbove i j = fun x => i.succAbove (((Fin.predAbove 0 i).predAbove j).succAbove x) := by
  rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨j, rfl⟩
  · contradiction
  · ext x
    rw [succSuccAbove_eq_succAbove_succAbove, Function.comp_apply]
    congr
    rcases eq_or_ne i 0 with rfl | hi
    · rfl
    · rw [Fin.predAbove_zero_of_ne_zero hi]
      rcases lt_or_ge (i.pred hi).castSucc (i.succAbove j) with h | h
      · rw [Fin.predAbove_of_castSucc_lt _ _ h, Fin.pred_succAbove]
        rw [← Fin.lt_succAbove_iff_le_castSucc]
        exact lt_of_le_of_ne ((Fin.castSucc_pred_lt_iff hi).mp h) hij
      · rw [Fin.predAbove_of_le_castSucc _ _ h, Fin.castPred_succAbove]
        rw [Fin.castSucc_lt_iff_succ_le, ← Fin.succAbove_lt_iff_succ_le]
        exact (Fin.le_castSucc_pred_iff hi).mp h
