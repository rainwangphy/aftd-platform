import AFTD.Prelude
import AFTD.Kb.Physics.Divergence
import AFTD.Kb.Physics.DivergenceEqSumFderiv
import AFTD.Kb.Physics.DivergenceZero

/-!
# divergence_eq_sum_fderiv'

Topic: classical_mechanics   Node: e2d681dd60b1

Provenance: formalization of a published result. Source: Physlib, `divergence_eq_sum_fderiv'`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

divergence_eq_sum_fderiv'
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
lemma divergence_eq_sum_fderiv' {ι} [Fintype ι] (b : Basis ι 𝕜 E) {f : E → E} :
    divergence 𝕜 f = fun x => ∑ i, b.repr (fderiv 𝕜 f x (b i)) i := by
  let s : Finset E := Finset.univ.map ⟨b, Basis.injective b⟩
  let f' : ι → s := fun i => ⟨b i, by simp [s]⟩
  have h : Function.Injective f' := by
    intro i j h
    simp [f'] at h
    exact Basis.injective b h
  have h' : Function.Surjective f' := by
    intro ⟨x, hx⟩
    simp [s] at hx
    obtain ⟨i, rfl⟩ := hx
    simp [f']
  let e : ι ≃ s := Equiv.ofBijective f' ⟨h, h'⟩
  let b' : Basis s 𝕜 E := b.reindex e
  rw [divergence_eq_sum_fderiv b']
  ext x
  rw [← e.symm.sum_comp]
  simp [b']
