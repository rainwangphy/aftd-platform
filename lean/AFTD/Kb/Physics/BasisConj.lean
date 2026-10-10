import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule
import AFTD.Kb.Physics.ConjModuleInvolution
import AFTD.Kb.Physics.ConjEquiv
import AFTD.Kb.Physics.ConjModuleStarFinsupp

/-!
# Basis.conj

Topic: classical_mechanics   Node: a1a76357c3d4

Provenance: formalization of a published result. Source: Physlib, `Basis.conj`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A basis of `M` transported to a basis of `ConjModule M`: the same basis vectors, with coordinates conjugated (`(Basis.conj b).repr v = star ∘ b.repr v`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ConjModule in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
variable {ι : Type*} in
/-- A basis of `M` transported to a basis of `ConjModule M`: the same basis vectors, with coordinates conjugated (`(Basis.conj b).repr v = star ∘ b.repr v`). -/
noncomputable def Basis.conj (b : Basis ι k M) : Basis ι k (ConjModule M) :=
  Basis.ofRepr
    (((conjEquiv (k := k) (M := M)).symm.trans b.repr).trans starFinsupp)
