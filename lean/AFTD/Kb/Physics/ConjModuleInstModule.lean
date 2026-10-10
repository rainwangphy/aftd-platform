import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup

/-!
# ConjModule.instModule

Topic: classical_mechanics   Node: 33dec174ff30

Provenance: formalization of a published result. Source: Physlib, `ConjModule.instModule`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The twisted action `r • v = star r • v`, obtained by restricting scalars along the conjugation ring endomorphism `starRingEnd k`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ConjModule in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
/-- The twisted action `r • v = star r • v`, obtained by restricting scalars along the conjugation ring endomorphism `starRingEnd k`. -/
instance ConjModule.instModule : Module k (ConjModule M) :=
  Module.compHom M (starRingEnd k)
