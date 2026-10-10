import AFTD.Prelude

/-!
# Physlib.List.drop_eraseIdx_succ

Topic: classical_mechanics   Node: 82acc3de2803

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.drop_eraseIdx_succ`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.drop_eraseIdx_succ
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.drop_eraseIdx_succ {I : Type} :
    (n : ℕ) → (r : List I) → (hn : n < r.length) →
    r[n] :: List.drop n (List.eraseIdx r n) = List.drop n r
  | 0, _, _=> by
    simp only [List.eraseIdx_zero, List.drop_tail, zero_add, List.drop_one, List.drop_zero]
    rw [@List.getElem_zero]
    exact List.cons_head_tail _
  | n+1, [], hn => by simp at hn
  | n+1, a::as, hn => by
    simp only [List.getElem_cons_succ, List.eraseIdx_cons_succ, List.drop_succ_cons]
    refine drop_eraseIdx_succ n as _
