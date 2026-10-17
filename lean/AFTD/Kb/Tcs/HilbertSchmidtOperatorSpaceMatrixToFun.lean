import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSCoordFun

/-!
# HilbertSchmidtOperatorSpace.matrixToFun

Topic: quantum   Node: 22d842753eae

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.matrixToFun`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

HilbertSchmidtOperatorSpace.matrixToFun
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
noncomputable def HilbertSchmidtOperatorSpace.matrixToFun :
    Matrix (HSIndex ℋ) (HSIndex ℋ) ℂ ≃ₗ[ℂ] HSCoordFun ℋ where
  toFun M p := M p.1 p.2
  invFun f i j := f (i, j)
  map_add' M N := by
    ext ⟨i, j⟩
    rfl
  map_smul' c M := by
    ext ⟨i, j⟩
    rfl
  left_inv M := by
    ext i j
    rfl
  right_inv f := by
    ext ⟨i, j⟩
    rfl
