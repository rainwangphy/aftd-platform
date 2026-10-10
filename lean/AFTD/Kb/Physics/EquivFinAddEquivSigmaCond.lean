import AFTD.Prelude
import AFTD.Kb.Physics.EquivSumEquivSigmalCond

/-!
# Equiv.finAddEquivSigmaCond

Topic: classical_mechanics   Node: 3bdd1f1edf5e

Provenance: formalization of a published result. Source: Physlib, `Equiv.finAddEquivSigmaCond`. Lean proof by Gordon Hsu, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/SchurTriangulation.lean (Copyright (c) 2025 Gordon Hsu. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The composition of `finSumFinEquiv` and `Equiv.sumEquivSigmalCond` used by `LinearMap.SchurTriangulationAux.of`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped InnerProductSpace in
open Module in
/-- The composition of `finSumFinEquiv` and `Equiv.sumEquivSigmalCond` used by `LinearMap.SchurTriangulationAux.of`. -/
def Equiv.finAddEquivSigmaCond : Fin (m + n) ≃ Σ b, cond b (Fin m) (Fin n) :=
  finSumFinEquiv.symm.trans sumEquivSigmalCond
