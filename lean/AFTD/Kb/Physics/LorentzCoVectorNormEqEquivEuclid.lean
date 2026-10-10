import AFTD.Prelude
import AFTD.Kb.Physics.LorentzCoVector
import AFTD.Kb.Physics.LorentzCoVectorInstNorm
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommMonoid
import AFTD.Kb.Physics.LorentzCoVectorInstModuleReal
import AFTD.Kb.Physics.LorentzCoVectorEquivEuclid
import AFTD.Kb.Physics.LorentzCoVectorInstAddCommGroup
import AFTD.Kb.Physics.LorentzCoVectorInstFiniteDimensionalReal

/-!
# Lorentz.CoVector.norm_eq_equivEuclid

Topic: special_relativity   Node: 540be89824fc

Provenance: formalization of a published result. Source: Physlib, `Lorentz.CoVector.norm_eq_equivEuclid`. Lean proof by Matteo Cipollina, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Tensors/RealTensor/CoVector/Basic.lean (Copyright (c) 2025 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.CoVector.norm_eq_equivEuclid
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
lemma Lorentz.CoVector.norm_eq_equivEuclid (d : ℕ) (v : CoVector d) :
    ‖v‖ = ‖equivEuclid d v‖ := rfl
