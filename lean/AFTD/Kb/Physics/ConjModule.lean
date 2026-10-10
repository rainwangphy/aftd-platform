import AFTD.Prelude

/-!
# ConjModule

Topic: classical_mechanics   Node: b514616d600e

Provenance: formalization of a published result. Source: Physlib, `ConjModule`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The conjugate module of `M`: the same additive group with the scalar action twisted by conjugation, `r • v = star r • v`. A type synonym so the twisted action stays off `M`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
/-- The conjugate module of `M`: the same additive group with the scalar action twisted by conjugation, `r • v = star r • v`. A type synonym so the twisted action stays off `M`. -/
def ConjModule (M : Type*) := M
