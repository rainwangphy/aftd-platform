import AFTD.Prelude

/-!
# QuantumMechanics.HarmonicOscillator

Topic: quantum_mechanics   Node: 6fc8265c6042

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.HarmonicOscillator`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The `d`-dimensional quantum harmonic oscillator.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
/-- The `d`-dimensional quantum harmonic oscillator. -/
structure QuantumMechanics.HarmonicOscillator (d : ℕ) where
  /-- The mass (positive). -/
  m : ℝ
  hm : 0 < m
  /-- The natural frequencies (positive). -/
  ω : Fin d → ℝ
  hω : ∀ i, 0 < ω i
