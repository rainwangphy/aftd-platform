import AFTD.Prelude
import AFTD.Kb.Physics.EquivFinAddEquivSigmaCond
import AFTD.Kb.Physics.FinSubNat'
import AFTD.Kb.Physics.EquivSumEquivSigmalCond

/-!
# Equiv.finAddEquivSigmaCond_false

Topic: classical_mechanics   Node: 28f85a58e88c

Provenance: formalization of a published result. Source: Physlib, `Equiv.finAddEquivSigmaCond_false`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Equiv.finAddEquivSigmaCond_false
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Equiv in
open scoped InnerProductSpace in
open Module in
variable {i : Fin (m + n)} in
lemma Equiv.finAddEquivSigmaCond_false (h : ¬ i < m) : finAddEquivSigmaCond i = ⟨false, i.subNat' h⟩ :=
  let j : Fin n := i.subNat' h
  calc finAddEquivSigmaCond i
    _ = finAddEquivSigmaCond (Fin.natAdd m j) :=
      suffices m + (i - m) = i from congrArg _ (Fin.ext this.symm)
      Nat.add_sub_of_le (Nat.le_of_not_gt h)
    _ = ⟨false, i.subNat' h⟩ := congrArg sumEquivSigmalCond <| finSumFinEquiv_symm_apply_natAdd j
