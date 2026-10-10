import AFTD.Prelude
import AFTD.Kb.Physics.LorentzSL2CToSelfAdjointMap

/-!
# Lorentz.SL2C.toSelfAdjointMap_apply

Topic: special_relativity   Node: 86995e1725f1

Provenance: formalization of a published result. Source: Physlib, `Lorentz.SL2C.toSelfAdjointMap_apply`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/SL2C/Basic.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lorentz.SL2C.toSelfAdjointMap_apply
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
lemma Lorentz.SL2C.toSelfAdjointMap_apply (A : selfAdjoint (Matrix (Fin 2) (Fin 2) ℂ)) :
    toSelfAdjointMap M A = ⟨M.1 * A.1 * Matrix.conjTranspose M, by
        noncomm_ring [selfAdjoint.mem_iff, star_eq_conjTranspose,
        conjTranspose_mul, conjTranspose_conjTranspose,
        (star_eq_conjTranspose A.1).symm.trans $ selfAdjoint.mem_iff.mp A.2]⟩ := rfl
