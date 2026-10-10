import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibListInsertIdxLengthFin
import AFTD.Kb.Tcs.ResolutionRefutationPosNegExample

/-!
# Physlib.List.insertIdx_getElem_fin

Topic: classical_mechanics   Node: 616f58d2aa4f

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_getElem_fin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_getElem_fin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.List in
open Physlib in
variable {n : Nat} in
@[simp]
lemma Physlib.List.insertIdx_getElem_fin {I : Type} (i : I) :
    (r : List I) → (k : Fin r.length.succ) → (m : Fin r.length) →
    (List.insertIdx r k i)[(k.succAbove m).val] = r[m.val]
  | [], 0, m => by exact Fin.elim0 m
  | a :: as, 0, m => by simp
  | a :: as, ⟨n + 1, h⟩, ⟨0, h0⟩ => by
    simp [Fin.succAbove, Fin.lt_def]
  | a :: as, ⟨n + 1, h⟩, ⟨m+1, hm⟩ => by
    simp only [List.insertIdx_succ_cons, List.length_cons, Nat.succ_eq_add_one,
      List.getElem_cons_succ]
    conv_rhs => rw [← insertIdx_getElem_fin i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩
      ⟨m, Nat.lt_of_succ_lt_succ hm⟩]
    simp only [Fin.succAbove, Fin.castSucc_mk, Fin.lt_def, add_lt_add_iff_right, Fin.succ_mk,
      Nat.succ_eq_add_one]
    split
    · simp_all only [List.getElem_cons_succ]
    · simp_all only [List.getElem_cons_succ]
