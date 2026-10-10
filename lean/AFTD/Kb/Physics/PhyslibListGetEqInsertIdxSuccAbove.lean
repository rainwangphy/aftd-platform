import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibListInsertIdxLengthFin
import AFTD.Kb.Physics.PhyslibListInsertIdxGetElemFin

/-!
# Physlib.List.get_eq_insertIdx_succAbove

Topic: classical_mechanics   Node: 9d4df2c53319

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.get_eq_insertIdx_succAbove`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.get_eq_insertIdx_succAbove
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.List in
open Physlib in
variable {n : Nat} in
lemma Physlib.List.get_eq_insertIdx_succAbove {I : Type} (i : I) (r : List I) (k : Fin r.length.succ) :
    r.get = (List.insertIdx r k i).get ∘
    (finCongr (insertIdx_length_fin i r k).symm) ∘ k.succAbove := by
  funext i
  simp
