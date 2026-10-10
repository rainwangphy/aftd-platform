import AFTD.Prelude

/-!
# Physlib.List.insertIdx_map

Topic: classical_mechanics   Node: 01a5de43b6bc

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_map`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_map
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.insertIdx_map {I J : Type} (f : I → J) : (i : ℕ) → (r : List I) → (r0 : I) →
    (List.insertIdx r i r0).map f = List.insertIdx (r.map f) i (f r0)
  | 0, [], r0 => by simp
  | n+1, [], r0 => by simp
  | 0, a::as, r0 => by simp
  | n+1, a::as, r0 => by
    simp only [List.insertIdx_succ_cons, List.map_cons, List.cons.injEq, true_and]
    exact insertIdx_map f n as r0
