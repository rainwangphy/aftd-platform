import AFTD.Prelude

/-!
# LinearPMap.IsLowerBound

Topic: quantum_mechanics   Node: e4b587d7b713

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.IsLowerBound`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`IsLowerBound T z c` is the property that `c * ‖x‖ ≤ ‖T x - z • x‖` for all `x : T.domain`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
/-- `IsLowerBound T z c` is the property that `c * ‖x‖ ≤ ‖T x - z • x‖` for all `x : T.domain`. -/
noncomputable def LinearPMap.IsLowerBound (T : H →ₗ.[ℂ] H) (z : ℂ) (c : ℝ) : Prop := ∀ x : T.domain, c * ‖x‖ ≤ ‖T x - z • x‖
