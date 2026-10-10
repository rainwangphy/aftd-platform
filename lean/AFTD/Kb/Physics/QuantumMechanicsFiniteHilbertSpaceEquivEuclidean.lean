import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsFiniteHilbertSpace

/-!
# QuantumMechanics.FiniteHilbertSpace.equivEuclidean

Topic: quantum_mechanics   Node: 57e0fd8b1371

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.FiniteHilbertSpace.equivEuclidean`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HilbertSpaces/FiniteTarget/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` given by `val`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
variable {d : Type*} [Fintype d] [DecidableEq d] in
/-- The equivalence between `FiniteHilbertSpace d` and `EuclideanSpace ℂ d` given by `val`. -/
def QuantumMechanics.FiniteHilbertSpace.equivEuclidean : FiniteHilbertSpace d ≃ EuclideanSpace ℂ d where
  toFun := val
  invFun := mk
  left_inv _ := rfl
  right_inv _ := rfl
