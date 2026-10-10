import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor
import AFTD.Kb.Physics.SUSYN1ChiralModule
import AFTD.Kb.Physics.SUSYN1InstAddCommGroupChiralModule
import AFTD.Kb.Physics.SUSYN1ChiralColorTau
import AFTD.Kb.Physics.ConjModuleInstModule
import AFTD.Kb.Physics.BasisConjReprApply
import AFTD.Kb.Physics.SUSYN1ChiralColorBarBar
import AFTD.Kb.Physics.SUSYN1ChiralColorBarTau
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup

/-!
# SUSY.N1.instModuleChiralModule

Topic: quantum_field_theory   Node: 9052462afb79

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.instModuleChiralModule`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

SUSY.N1.instModuleChiralModule
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
noncomputable instance SUSY.N1.instModuleChiralModule : ∀ c, Module ℂ (chiralModule (ι := ι) c) | .chiralUp | .chiralDown | .antiUp | .antiDown => inferInstance
