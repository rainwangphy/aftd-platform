import AFTD.Prelude

/-!
# LinearPMap.numericalRange

Topic: quantum_mechanics   Node: e428c0edc9d7

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.numericalRange`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The set `{⟪x, T x⟫_ℂ | x ∈ T.domain ∧ ‖x‖ = 1} ⊆ ℂ`.
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
/-- The set `{⟪x, T x⟫_ℂ | x ∈ T.domain ∧ ‖x‖ = 1} ⊆ ℂ`. -/
noncomputable def LinearPMap.numericalRange (T : H →ₗ.[ℂ] H) : Set ℂ := (fun x ↦ ⟪↑x, T x⟫_ℂ) '' {x : T.domain | ‖x‖ = 1}
