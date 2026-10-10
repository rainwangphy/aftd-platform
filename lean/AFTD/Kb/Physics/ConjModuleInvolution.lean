import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule
import AFTD.Kb.Physics.ConjEquiv

/-!
# ConjModule.involution

Topic: classical_mechanics   Node: 4f44e22090f7

Provenance: formalization of a published result. Source: Physlib, `ConjModule.involution`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Conjugating twice returns the original module: the `k`-linear isomorphism `ConjModule (ConjModule M) ≃ₗ[k] M`. It is `k`-linear, not merely semilinear, because `starRingEnd k` composed with itself is the identity.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ConjModule in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
/-- Conjugating twice returns the original module: the `k`-linear isomorphism `ConjModule (ConjModule M) ≃ₗ[k] M`. It is `k`-linear, not merely semilinear, because `starRingEnd k` composed with itself is the identity. -/
def ConjModule.involution : ConjModule (ConjModule M) ≃ₗ[k] M :=
  ((conjEquiv (k := k) (M := M)).trans (conjEquiv (k := k) (M := ConjModule M))).symm
