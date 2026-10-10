import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisInlApplyInr

/-!
# Lorentz.ContrMod.mulVec

Topic: special_relativity   Node: 09308d62827b

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.mulVec`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Multiplication of a matrix with a vector in `ContrMod`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- Multiplication of a matrix with a vector in `ContrMod`. -/
noncomputable abbrev Lorentz.ContrMod.mulVec (M : Matrix (Fin 1 ⊕ Fin d) (Fin 1 ⊕ Fin d) ℝ) (v : ContrMod d) :
    ContrMod d := Matrix.toLinAlgEquiv stdBasis M v
