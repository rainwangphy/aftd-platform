import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor
import AFTD.Kb.Physics.SUSYN1ChiralModule
import AFTD.Kb.Physics.SUSYN1InstAddCommGroupChiralModule
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule
import AFTD.Kb.Physics.BasisConjReprApply
import AFTD.Kb.Physics.SUSYN1ChiralColorBarBar
import AFTD.Kb.Physics.SUSYN1ChiralColorBarTau
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule

/-!
# SUSY.N1.chiralRep

Topic: quantum_field_theory   Node: 44f0ef1fff04

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.chiralRep`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The representation on each colour, taken trivial over the trivial group `Unit`: the chiral scalars carry no charge in this sector.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
/-- The representation on each colour, taken trivial over the trivial group `Unit`: the chiral scalars carry no charge in this sector. -/
noncomputable def SUSY.N1.chiralRep : (c : ChiralColor) → Representation ℂ Unit (chiralModule (ι := ι) c) :=
  fun _ => Representation.trivial ℂ Unit _
