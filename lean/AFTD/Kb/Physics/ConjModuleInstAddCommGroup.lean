import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule

/-!
# ConjModule.instAddCommGroup

Topic: classical_mechanics   Node: fbd328cf9e7b

Provenance: formalization of a published result. Source: Physlib, `ConjModule.instAddCommGroup`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ConjModule.instAddCommGroup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
instance ConjModule.instAddCommGroup : AddCommGroup (ConjModule M) := inferInstanceAs (AddCommGroup M)
