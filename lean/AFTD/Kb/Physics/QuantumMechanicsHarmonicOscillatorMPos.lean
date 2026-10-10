import AFTD.Prelude
import AFTD.Kb.Physics.QuantumMechanicsHarmonicOscillator

/-!
# QuantumMechanics.HarmonicOscillator.m_pos

Topic: quantum_mechanics   Node: c754d0826c2b

Provenance: formalization of a published result. Source: Physlib, `QuantumMechanics.HarmonicOscillator.m_pos`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/QuantumMechanics/HarmonicOscillator/Basic.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

QuantumMechanics.HarmonicOscillator.m_pos
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open QuantumMechanics in
variable {d : ℕ} (Q : HarmonicOscillator d) (i : Fin d) in
open MeasureTheory in
@[simp]
lemma QuantumMechanics.HarmonicOscillator.m_pos : 0 < Q.m := Q.hm
