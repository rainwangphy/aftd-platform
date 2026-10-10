import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModToFin1dREquiv
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul

/-!
# Lorentz.ContrMod.stdBasis

Topic: special_relativity   Node: aa1bc050e333

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The standard basis of `ContrMod` indexed by `Fin 1 ⊕ Fin d`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- The standard basis of `ContrMod` indexed by `Fin 1 ⊕ Fin d`. -/
noncomputable def Lorentz.ContrMod.stdBasis : Basis (Fin 1 ⊕ Fin d) ℝ (ContrMod d) := Basis.ofEquivFun toFin1dℝEquiv
