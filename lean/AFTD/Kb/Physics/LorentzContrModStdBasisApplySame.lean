import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul

/-!
# Lorentz.ContrMod.stdBasis_apply_same

Topic: special_relativity   Node: c3460cf3c30d

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis_apply_same`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.stdBasis_apply_same
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
@[simp]
lemma Lorentz.ContrMod.stdBasis_apply_same (μ : Fin 1 ⊕ Fin d) : (stdBasis μ).val μ = 1 :=
  stdBasis_toFin1dℝEquiv_apply_same μ
