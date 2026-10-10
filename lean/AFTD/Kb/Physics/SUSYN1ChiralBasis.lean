import AFTD.Prelude
import AFTD.Kb.Physics.SUSYN1ChiralColor
import AFTD.Kb.Physics.SUSYN1ChiralModule
import AFTD.Kb.Physics.SUSYN1InstAddCommGroupChiralModule
import AFTD.Kb.Physics.SUSYN1InstModuleChiralModule
import AFTD.Kb.Physics.SUSYN1ChiralColorTau
import AFTD.Kb.Physics.SUSYN1PiBasis
import AFTD.Kb.Physics.BasisConj
import AFTD.Kb.Physics.BasisConjReprApply
import AFTD.Kb.Physics.BasisConjApply
import AFTD.Kb.Physics.SUSYN1ChiralColorBarBar
import AFTD.Kb.Physics.SUSYN1ChiralColorBarTau
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule

/-!
# SUSY.N1.chiralBasis

Topic: quantum_field_theory   Node: 269d52264728

Provenance: formalization of a published result. Source: Physlib, `SUSY.N1.chiralBasis`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Particles/SuperSymmetry/N1/Basic.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The basis of each colour's carrier, all indexed by `ι`: `piBasis` on the holomorphic vectors, its dual `piBasis.dualBasis` on the holomorphic covectors, and the `Basis.conj` of each on the anti-holomorphic side (coordinates `star`-ed).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open SUSY SUSY.N1 in
open TensorProduct Module ComplexConjugate in
variable (ι : Type) [Fintype ι] [DecidableEq ι] in
variable {ι} in
/-- The basis of each colour's carrier, all indexed by `ι`: `piBasis` on the holomorphic vectors, its dual `piBasis.dualBasis` on the holomorphic covectors, and the `Basis.conj` of each on the anti-holomorphic side (coordinates `star`-ed). -/
noncomputable def SUSY.N1.chiralBasis : (c : ChiralColor) → Basis ι ℂ (chiralModule (ι := ι) c)
  | .chiralUp   => piBasis
  | .chiralDown => piBasis.dualBasis
  | .antiUp     => Basis.conj piBasis
  | .antiDown   => Basis.conj piBasis.dualBasis
