import AFTD.Prelude

/-!
# Norm₂

Topic: classical_mechanics   Node: ad107dfb47fc

Provenance: formalization of a published result. Source: Physlib, `Norm₂`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/InnerProductSpace/Basic.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

L₂ norm on `E`. In particular, on product types `X×Y` and pi types `ι → X` this class provides L₂ norm unlike `‖·‖`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- L₂ norm on `E`. In particular, on product types `X×Y` and pi types `ι → X` this class provides L₂ norm unlike `‖·‖`. -/
class Norm₂ (E : Type*) where
  norm₂ : E → ℝ
