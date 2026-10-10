import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor
import AFTD.Kb.Physics.SUSYN1ChiralColorBar

/-!
# SUSY.N1.ChiralColor.bar_bar

Topic: quantum_field_theory   Node: 52623af6d464

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.ChiralColor.bar_bar`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SUSY.N1.ChiralColor.bar_bar
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 SUSY.N1.ChiralColor in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
@[simp] lemma SUSY.N1.ChiralColor.bar_bar (c : ChiralColor) : bar (bar c) = c := by cases c <;> rfl
