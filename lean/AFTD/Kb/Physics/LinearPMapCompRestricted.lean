import AFTD.Prelude
import AFTD.Kb.Physics.LinearPMapSum
import AFTD.Kb.Physics.LinearPMapSumApply

/-!
# LinearPMap.compRestricted

Topic: classical_mechanics   Node: a427a768b1cf

Provenance: formalization of a published result. Source: Physlib, `LinearPMap.compRestricted`. Lean proof by Gregory J. Loges, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/LinearPMap.lean (Copyright (c) 2026 Gregory J. Loges. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`g ∘ᵣ f` is the composition of `g` with `f` restricted to a domain consisting of exactly those `x : f.domain` for which `f x ∈ g.domain`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LinearPMap in
open Submodule in
variable {R : Type*} [Ring R] in
variable {E : Type*} [AddCommGroup E] [Module R E] in
variable {F : Type*} [AddCommGroup F] [Module R F] in
variable {G : Type*} [AddCommGroup G] [Module R G] in
variable (g g₁ g₂ : F →ₗ.[R] G) (f f₁ f₂ : E →ₗ.[R] F) in
variable {v : F →ₗ.[R] G} {u : E →ₗ.[R] F} in
/-- `g ∘ᵣ f` is the composition of `g` with `f` restricted to a domain consisting of exactly those `x : f.domain` for which `f x ∈ g.domain`. -/
def LinearPMap.compRestricted : E →ₗ.[R] G :=
  g.comp (f.domRestrict <| (g.domain.comap f.toFun).map f.domain.subtype) (by
    intro x
    have h : (x : E) ∈ (g.domain.comap f.toFun).map f.domain.subtype := x.2.1
    simp only [mem_map, mem_comap, toFun_eq_coe, subtype_apply] at h
    obtain ⟨y, hy, hy'⟩ := h
    rw [domRestrict_apply hy'.symm]
    exact hy)
