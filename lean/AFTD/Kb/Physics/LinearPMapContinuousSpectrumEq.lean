import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapContinuousSpectrum
import AFTD.Kb.Physics.LinearPMapInstMonoid

/-!
# LinearPMap.continuousSpectrum_eq

Topic: quantum_mechanics   Node: 8780b0df0376

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.continuousSpectrum_eq`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.continuousSpectrum_eq
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc spectrum]
local notation "σ" => spectrum
open LinearPMap
@[inherit_doc continuousSpectrum]
local notation "σᶜ" => continuousSpectrum

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] in
open Submodule in
open Metric in
open InnerProductSpace in
open Complex in
open ComplexConjugate in
open Set in
open Pointwise in
lemma LinearPMap.continuousSpectrum_eq (T : H →ₗ.[ℂ] H) :
    σᶜ T = {z | ¬_root_.IsClosed ((T - z • 1).toFun.range : Set H)} := rfl
