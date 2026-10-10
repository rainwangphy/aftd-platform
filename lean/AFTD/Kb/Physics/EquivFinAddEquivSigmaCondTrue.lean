import AFTD.Prelude
import AFTD.Kb.Physics.EquivFinAddEquivSigmaCond
import AFTD.Kb.Physics.EquivSumEquivSigmalCond

/-!
# Equiv.finAddEquivSigmaCond_true

Topic: classical_mechanics   Node: 6982256c11c1

Provenance: formalization of a published result. Source: Physlib, `Equiv.finAddEquivSigmaCond_true`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equiv.finAddEquivSigmaCond_true
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Equiv in
open scoped InnerProductSpace in
open Module in
variable {i : Fin (m + n)} in
lemma Equiv.finAddEquivSigmaCond_true (h : i < m) : finAddEquivSigmaCond i = ⟨true, i, h⟩ :=
  congrArg sumEquivSigmalCond <| finSumFinEquiv_symm_apply_castAdd ⟨i, h⟩
