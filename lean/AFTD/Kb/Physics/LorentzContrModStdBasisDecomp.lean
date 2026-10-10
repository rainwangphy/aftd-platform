import AFTD.Prelude
import AFTD.Kb.Physics.LorentzContrMod
import AFTD.Kb.Physics.LorentzContrModInstAddCommGroup
import AFTD.Kb.Physics.LorentzContrModInstModuleReal
import AFTD.Kb.Physics.LorentzContrModToFin1dR
import AFTD.Kb.Physics.LorentzContrModStdBasis
import AFTD.Kb.Physics.LorentzContrModToFin1dREquiv
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplyNe
import AFTD.Kb.Physics.LorentzContrModStdBasisToFin1dREquivApplySame
import AFTD.Kb.Physics.LorentzContrModValAdd
import AFTD.Kb.Physics.LorentzContrModValSmul
import AFTD.Kb.Physics.LorentzContrModStdBasisApplySame
import AFTD.Kb.Physics.LorentzContrModStdBasisInlApplyInr

/-!
# Lorentz.ContrMod.stdBasis_decomp

Topic: special_relativity   Node: d0f968210b62

Provenance: formalization of a published result. Source: Physlib, `Lorentz.ContrMod.stdBasis_decomp`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/Vector/Pre/Modules.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Decomposition of a contravariant Lorentz vector into the standard basis.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Lorentz Lorentz.ContrMod in
open Matrix Module MatrixGroups Complex in
variable {d : ℕ} in
/-- Decomposition of a contravariant Lorentz vector into the standard basis. -/
lemma Lorentz.ContrMod.stdBasis_decomp (v : ContrMod d) : v = ∑ i, v.toFin1dℝ i • stdBasis i := by
  apply toFin1dℝEquiv.injective
  simp only [map_sum, _root_.map_smul]
  funext μ
  rw [Fintype.sum_apply μ fun c => toFin1dℝEquiv v c • toFin1dℝEquiv (stdBasis c)]
  change _ = ∑ x : Fin 1 ⊕ Fin d, toFin1dℝEquiv v x • (toFin1dℝEquiv (stdBasis x) μ)
  rw [Finset.sum_eq_single_of_mem μ (Finset.mem_univ μ)]
  · simp only [stdBasis_toFin1dℝEquiv_apply_same, smul_eq_mul, mul_one]
  · intro b _ hbμ
    rw [stdBasis_toFin1dℝEquiv_apply_ne hbμ]
    simp only [smul_eq_mul, mul_zero]
