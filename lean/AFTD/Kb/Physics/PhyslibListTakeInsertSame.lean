import AFTD.Prelude

/-!
# Physlib.List.take_insert_same

Topic: classical_mechanics   Node: 7e801ed0f5e5

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.take_insert_same`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.take_insert_same
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.take_insert_same {I : Type} (i : I) :
    (n : ℕ) → (r : List I) →
    List.take n (List.insertIdx r n i) = List.take n r
  | 0, _ => by simp
  | _+1, [] => by simp
  | n+1, a::as => by
    simp only [List.insertIdx_succ_cons, List.take_succ_cons, List.cons.injEq, true_and]
    exact take_insert_same i n as
