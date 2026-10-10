import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibListInsertIdxGetElemFin

/-!
# Physlib.List.insertIdx_eraseIdx_fin

Topic: classical_mechanics   Node: a3ecacda1252

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_eraseIdx_fin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_eraseIdx_fin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.List in
open Physlib in
variable {n : Nat} in
lemma Physlib.List.insertIdx_eraseIdx_fin {I : Type} :
    (r : List I) → (k : Fin r.length) →
    (List.eraseIdx r k).insertIdx k r[k] = r
  | [], k => by exact Fin.elim0 k
  | a :: as, ⟨0, h⟩ => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp only [List.length_cons, Fin.getElem_fin, List.getElem_cons_succ, List.eraseIdx_cons_succ,
      List.insertIdx_succ_cons, List.cons.injEq, true_and]
    exact insertIdx_eraseIdx_fin as ⟨n, Nat.lt_of_succ_lt_succ h⟩
