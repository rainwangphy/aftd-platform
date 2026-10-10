import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibFinInvolutionNoFixedSetOne

/-!
# Physlib.List.insertIdx_length_fin

Topic: classical_mechanics   Node: 7e7a7ccf085d

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.insertIdx_length_fin`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.insertIdx_length_fin
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
@[simp]
lemma Physlib.List.insertIdx_length_fin {I : Type} (i : I) :
    (r : List I) → (n : Fin r.length.succ) →
    (List.insertIdx r n i).length = r.length.succ
  | [], 0 => by simp
  | a :: as, 0 => by simp
  | a :: as, ⟨n + 1, h⟩ => by
    simp only [List.insertIdx_succ_cons, List.length_cons, Nat.succ_eq_add_one, add_left_inj]
    exact insertIdx_length_fin i as ⟨n, Nat.succ_lt_succ_iff.mp h⟩
