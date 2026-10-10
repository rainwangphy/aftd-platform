import AFTD.Prelude

/-!
# Physlib.List.insertIdx_eq_take_drop

Topic: classical_mechanics   Node: 151afab5b8c9

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_eq_take_drop`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_eq_take_drop
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.insertIdx_eq_take_drop {I : Type} (i : I) : (r : List I) → (n : Fin r.length.succ) →
    List.insertIdx r n i = List.take n r ++ i :: r.drop n
  | [], 0 => by simp
  | a :: as, 0 => by
    simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.drop_succ_cons, List.cons_append,
      List.cons.injEq, true_and]
    exact insertIdx_eq_take_drop i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩
