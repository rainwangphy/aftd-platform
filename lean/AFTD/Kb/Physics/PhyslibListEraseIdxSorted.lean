import AFTD.Prelude

/-!
# Physlib.List.eraseIdx_sorted

Topic: classical_mechanics   Node: 0107f1e3f400

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.eraseIdx_sorted`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.eraseIdx_sorted
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.eraseIdx_sorted {I : Type} (le : I → I → Prop) :
    (r : List I) → (n : ℕ) →
    List.Pairwise le r → List.Pairwise le (r.eraseIdx n)
  | [], _, _ => by simp
  | a::as, 0, h => by
    simp only [List.eraseIdx]
    simp only [List.pairwise_cons] at h
    exact h.2
  | a::as, n+1, h => by
    simp only [List.eraseIdx_cons_succ, List.pairwise_cons]
    simp only [List.pairwise_cons] at h
    refine And.intro ?_ (eraseIdx_sorted le as n h.2)
    intro b hb
    refine h.1 _ ?_
    exact List.mem_of_mem_eraseIdx hb
