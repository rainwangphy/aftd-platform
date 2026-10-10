import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapPointSpectrum
import AFTD.Kb.Physics.LinearPMapInstMonoid

/-!
# LinearPMap.mem_pointSpectrum_iff

Topic: quantum_mechanics   Node: e45386162772

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.mem_pointSpectrum_iff`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/Operators/SpectralTheory/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LinearPMap.mem_pointSpectrum_iff
-/

set_option quotPrecheck false
open LinearPMap
@[inherit_doc spectrum]
local notation "σ" => spectrum
open LinearPMap
@[inherit_doc pointSpectrum]
local notation "σᵖ" => pointSpectrum

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
lemma LinearPMap.mem_pointSpectrum_iff {T : H →ₗ.[ℂ] H} {z : ℂ} : z ∈ σᵖ T ↔ (T - z • 1).toFun.ker ≠ ⊥ :=
  Iff.rfl
