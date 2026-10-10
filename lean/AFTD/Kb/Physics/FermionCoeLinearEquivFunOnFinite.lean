import AFTD.Prelude

/-!
# Fermion.coe_linearEquivFunOnFinite

Topic: special_relativity   Node: 9b0de4c050ff

Provenance: formalization of a published result. Source: Physlib, `Fermion.coe_linearEquivFunOnFinite`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Relativity/Fermions/Weyl/Two.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The coercion of `Finsupp.linearEquivFunOnFinite` to a function is the underlying finitely-supported function, used to bridge it with `Matrix.mulVec`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module Matrix in
open MatrixGroups in
open Complex in
open TensorProduct in
open CategoryTheory.MonoidalCategory in
/-- The coercion of `Finsupp.linearEquivFunOnFinite` to a function is the underlying finitely-supported function, used to bridge it with `Matrix.mulVec`. -/
lemma Fermion.coe_linearEquivFunOnFinite (g : (Fin 2 × Fin 2) →₀ ℂ) :
    Finsupp.linearEquivFunOnFinite ℂ ℂ (Fin 2 × Fin 2) g = ⇑g := rfl
