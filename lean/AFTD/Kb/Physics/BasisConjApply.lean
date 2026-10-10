import AFTD.Prelude
import AFTD.Kb.Physics.ConjModule
import AFTD.Kb.Physics.ConjModuleInstAddCommGroup
import AFTD.Kb.Physics.ConjModuleInstModule
import AFTD.Kb.Physics.BasisConj
import AFTD.Kb.Physics.ConjEquiv
import AFTD.Kb.Physics.BasisConjReprApply

/-!
# Basis.conj_apply

Topic: classical_mechanics   Node: 32deec2bc5e3

Provenance: formalization of a published result. Source: Physlib, `Basis.conj_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Modules/ConjModule.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The basis vectors of `Basis.conj b` are those of `b`, viewed through `conjEquiv`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open ConjModule in
open Module in
variable {k : Type*} [CommRing k] [StarRing k] in
variable {M : Type*} [AddCommGroup M] [Module k M] in
variable {ι : Type*} in
/-- The basis vectors of `Basis.conj b` are those of `b`, viewed through `conjEquiv`. -/
@[simp] lemma Basis.conj_apply (b : Basis ι k M) (i : ι) :
    Basis.conj b i = conjEquiv (k := k) (M := M) (b i) := by
  apply (Basis.conj b).repr.injective
  ext j
  rcases eq_or_ne j i with h | h
  · subst h; simp [Basis.conj_repr_apply]
  · simp [Basis.conj_repr_apply, Finsupp.single_eq_of_ne, h]
