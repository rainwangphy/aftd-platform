import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillator
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillatorMPos
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillatorMNonneg
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillatorMNeZero
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillatorOmegaPos

/-!
# QuantumMechanics.HarmonicOscillator.ω_nonneg

Topic: quantum_mechanics   Node: 27dd7f82332b

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.HarmonicOscillator.ω_nonneg`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.HarmonicOscillator.ω_nonneg
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d) in
open MeasureTheory in
@[simp]
lemma QuantumMechanics.HarmonicOscillator.ω_nonneg : 0 ≤ Q.ω i := (Q.hω i).le
