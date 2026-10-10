import AFTD.Prelude

/-!
# lorentzAlgebra

Topic: special_relativity   Node: c56cec974919

Provenance: formalization of a published result. Source: Physlib, `lorentzAlgebra`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/LorentzAlgebra/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Lorentz algebra as a subalgebra of `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open TensorProduct in
attribute [local instance 100] LieRing.ofAssociativeRing in
/-- The Lorentz algebra as a subalgebra of `Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ`. -/
def lorentzAlgebra : LieSubalgebra ℝ (Matrix (Fin 1 ⊕ Fin 3) (Fin 1 ⊕ Fin 3) ℝ) :=
  (LieAlgebra.Orthogonal.so' (Fin 1) (Fin 3) ℝ)
