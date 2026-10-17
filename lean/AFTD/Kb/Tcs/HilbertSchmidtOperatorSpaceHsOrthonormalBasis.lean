import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex

/-!
# HilbertSchmidtOperatorSpace.hsOrthonormalBasis

Topic: quantum   Node: 568d128c7a35

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.hsOrthonormalBasis`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard orthonormal basis on a finite-dimensional Hilbert space.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
/-- The standard orthonormal basis on a finite-dimensional Hilbert space. -/
noncomputable abbrev HilbertSchmidtOperatorSpace.hsOrthonormalBasis :
    OrthonormalBasis (HSIndex ℋ) ℂ ℋ :=
  stdOrthonormalBasis ℂ ℋ
