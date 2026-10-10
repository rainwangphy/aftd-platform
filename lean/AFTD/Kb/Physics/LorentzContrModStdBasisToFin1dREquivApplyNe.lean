import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModToFin1dREquiv
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisApplySame

/-!
# Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_ne

Topic: special_relativity   Node: db5d4a3305f3

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_ne`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_ne
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
lemma Lorentz.ContrMod.stdBasis_toFin1dℝEquiv_apply_ne {μ ν : Fin 1 ⊕ Fin d} (h : μ ≠ ν) :
    toFin1dℝEquiv (stdBasis μ) ν = 0 := by
  simp only [stdBasis, Basis.ofEquivFun, Basis.coe_ofRepr, LinearEquiv.trans_symm,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, Finsupp.linearEquivFunOnFinite_single]
  rw [@LinearEquiv.apply_symm_apply]
  exact Pi.single_eq_of_ne' h 1
