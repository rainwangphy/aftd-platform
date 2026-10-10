import AFTD.Prelude

/-!
# Physlib.List.insertIdx_length_fst_append

Topic: classical_mechanics   Node: 70951865db59

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_length_fst_append`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_length_fst_append
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.insertIdx_length_fst_append {I : Type} (φ : I) : (φs φs' : List I) →
    List.insertIdx (φs ++ φs') φs.length φ = (φs ++ φ :: φs')
  | [], φs' => by simp
  | φ' :: φs, φs' => by
    simp only [List.length_cons, List.cons_append, List.insertIdx_succ_cons, List.cons.injEq,
      true_and]
    exact insertIdx_length_fst_append φ φs φs'
