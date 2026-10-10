import AFTD.Prelude

/-!
# Physlib.Distribution

Topic: classical_mechanics   Node: dfe37312bae5

Provenance: formalization of a published result. Source: Physlib, `Physlib.Distribution`. Lean proof by Kenny Lau, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Distribution/Basic.lean (Copyright (c) 2025 Kenny Lau. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

An `F`-valued distribution on `E` (where `E` is a normed vector space over `ℝ` and `F` is a normed vector space over `𝕜`) is a continuous linear map `𝓢(E, 𝕜) →L[𝕜] F` where `𝒮(E, 𝕜)` is the Schwartz space of smooth functions `E → 𝕜` with rapidly decreasing iterated derivatives. This is notated as `E →d[𝕜] F`. This should be seen as a generalisation of functions `E → F`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SchwartzMap NNReal in
open scoped ENNReal SchwartzMap FourierTransform in
/-- An `F`-valued distribution on `E` (where `E` is a normed vector space over `ℝ` and `F` is a normed vector space over `𝕜`) is a continuous linear map `𝓢(E, 𝕜) →L[𝕜] F` where `𝒮(E, 𝕜)` is the Schwartz space of smooth functions `E → 𝕜` with rapidly decreasing iterated derivatives. This is notated as `E →d[𝕜] F`. This should be seen as a generalisation of functions `E → F`. -/
noncomputable abbrev Physlib.Distribution (𝕜 E F : Type) [RCLike 𝕜] [NormedAddCommGroup E] [NormedAddCommGroup F]
    [NormedSpace ℝ E] [NormedSpace 𝕜 F] : Type :=
  𝓢(E, 𝕜) →L[𝕜] F
