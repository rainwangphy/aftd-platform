import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule
import AFTD.Kb.Physics.BasisConj
import AFTD.Kb.Physics.ConjEquiv

/-!
# Basis.conj_repr_apply

Topic: classical_mechanics   Node: a60c10cb47b3

Provenance: formalization of a published result. Source: Physlib, `Basis.conj_repr_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Coordinates in `Basis.conj b` are the `star` of the coordinates in `b`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ConjModule in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
variable {ι : Type*} in
/-- Coordinates in `Basis.conj b` are the `star` of the coordinates in `b`. -/
@[simp] lemma Basis.conj_repr_apply (b : Basis ι k M) (v : ConjModule M) (i : ι) :
    (Basis.conj b).repr v i = star (b.repr ((conjEquiv (k := k) (M := M)).symm v) i) := rfl
