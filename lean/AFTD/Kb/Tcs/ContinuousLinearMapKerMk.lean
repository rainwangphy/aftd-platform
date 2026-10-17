import AFTD.Prelude

/-!
# ContinuousLinearMap.ker_mk

Topic: quantum   Node: 1f4581180925

Provenance: formalization of a published result. Source: QuantumInfo, `ContinuousLinearMap.ker_mk`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/ContinuousLinearMap.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ContinuousLinearMap.ker_mk
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ContinuousLinearMap in
variable {R S : Type*} [Semiring R] [Semiring S] (σ : R →+* S) (M M₂ : Type*) in
variable [TopologicalSpace M] [AddCommMonoid M] [TopologicalSpace M₂] [AddCommMonoid M₂] in
variable [Module R M] [Module S M₂] in
theorem ContinuousLinearMap.ker_mk (f : M →ₛₗ[σ] M₂) (hf : Continuous f.toFun) :
    (ContinuousLinearMap.mk f hf).ker = LinearMap.ker f := by
  rfl
