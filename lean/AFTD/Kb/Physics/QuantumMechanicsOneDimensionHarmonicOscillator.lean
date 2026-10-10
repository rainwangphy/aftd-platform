import AFTD.Prelude

/-!
# QuantumMechanics.OneDimension.HarmonicOscillator

Topic: quantum_mechanics   Node: fc9c9a3c51e1

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.OneDimension.HarmonicOscillator`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/OneDimension/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A quantum harmonic oscillator specified by a three real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and an angular frequency `ω`. All three of these parameters are assumed to be positive.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- A quantum harmonic oscillator specified by a three real parameters: the mass of the particle `m`, a value of Planck's constant `ℏ`, and an angular frequency `ω`. All three of these parameters are assumed to be positive. -/
structure QuantumMechanics.OneDimension.HarmonicOscillator where
  /-- The mass of the particle. -/
  m : ℝ
  /-- The angular frequency of the harmonic oscillator. -/
  ω : ℝ
  hω : 0 < ω
  hm : 0 < m
