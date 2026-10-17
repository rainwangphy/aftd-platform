import AFTD.Prelude

/-!
# HilbertSchmidtOperatorSpace.HSIndex

Topic: quantum   Node: 5b892b3f1b6c

Provenance: formalization of a published result. Source: QuantumInfo, `HilbertSchmidtOperatorSpace.HSIndex`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/HilbertSchmidtOperatorSpace.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The canonical finite index used for Hilbert-Schmidt coordinates.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u in
variable {ℋ : Type u} in
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] in
variable [FiniteDimensional ℂ ℋ] in
/-- The canonical finite index used for Hilbert-Schmidt coordinates. -/
noncomputable abbrev HilbertSchmidtOperatorSpace.HSIndex (ℋ : Type u) [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ]
    [FiniteDimensional ℂ ℋ] :=
  Fin (Module.finrank ℂ ℋ)
