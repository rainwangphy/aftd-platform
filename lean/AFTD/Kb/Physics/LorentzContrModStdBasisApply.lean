import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModToFin1dREquiv
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisInlApplyInr

/-!
# Lorentz.ContrMod.stdBasis_apply

Topic: special_relativity   Node: c7eb9cbf678a

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.stdBasis_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
lemma Lorentz.ContrMod.stdBasis_apply (μ ν : Fin 1 ⊕ Fin d) : (stdBasis μ).val ν = if μ = ν then 1 else 0 := by
  simp only [stdBasis, Basis.coe_ofEquivFun]
  change Pi.single μ 1 ν = _
  simp only [Pi.single_apply]
  refine ite_congr ?h₁ (congrFun rfl) (congrFun rfl)
  exact Eq.propIntro (fun a => id (Eq.symm a)) fun a => id (Eq.symm a)
