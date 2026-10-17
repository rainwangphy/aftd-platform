import AFTD.Prelude
import AFTD.Kb.Tcs.HilbertSchmidtOperatorSpaceHSIndex

/-!
# HilbertSchmidtOperatorSpace.HSCoords

Topic: quantum   Node: 00cc23a38526

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.HSCoords`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coordinate space for Hilbert-Schmidt operators.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open HilbertSchmidtOperatorSpace in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
/-- Coordinate space for Hilbert-Schmidt operators. -/
noncomputable abbrev HilbertSchmidtOperatorSpace.HSCoords (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  EuclideanSpace ℂ (HSIndex ℋ × HSIndex ℋ)
