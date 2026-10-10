import AFTD.Prelude

/-!
# TriLinearSymm

Topic: classical_mechanics   Node: 4b21c20dbc27

Provenance: formalization of a published result. Source: Physlib, `TriLinearSymm`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearMaps.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The structure of a symmetric trilinear function.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The structure of a symmetric trilinear function. -/
structure TriLinearSymm (V : Type) [AddCommMonoid V] [Module ℚ V] extends
    V →ₗ[ℚ] V →ₗ[ℚ] V →ₗ[ℚ] ℚ where
  swap₁' : ∀ S T L, toFun S T L = toFun T S L
  swap₂' : ∀ S T L, toFun S T L = toFun S L T
