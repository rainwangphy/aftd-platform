import AFTD.Prelude
import AFTD.Kb.Physics.SpaceTimeGammaDiracForm

/-!
# PauliMatrix.form

Topic: special_relativity   Node: 9581b344a323

Provenance: formalization of a published result. Source: Physlib, `PauliMatrix.form`. Lean proof by Eric Wieser, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/PauliMatrices/CliffordAlgebra.lean (Copyright (c) 2025 Eric Wieser. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The euclidean norm as a quadratic form.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The euclidean norm as a quadratic form. -/
@[simps!]
protected noncomputable def PauliMatrix.form : QuadraticForm ℝ (Fin 3 → ℝ) :=
  ∑ i, QuadraticMap.sq.comp (LinearMap.proj i)
