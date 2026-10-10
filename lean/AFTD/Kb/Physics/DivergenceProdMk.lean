import AFTD.Prelude
import AFTD.Kb.Physics.Divergence
import AFTD.Kb.Physics.DivergenceEqSumFderiv'
import AFTD.Kb.Physics.FderivWrtProd
import AFTD.Kb.Physics.DivergenceZero

/-!
# divergence_prodMk

Topic: classical_mechanics   Node: 0bf4e707cd72

Provenance: formalization of a published result. Source: Physlib, `divergence_prodMk`. Lean proof by Tomas Skrivan, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Divergence.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

divergence_prodMk
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
open scoped InnerProductSpace in
variable
  {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] in
lemma divergence_prodMk [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    {f : E×F → E} {g : E×F → F} {xy : E×F}
    (hf : DifferentiableAt 𝕜 f xy) (hg : DifferentiableAt 𝕜 g xy) :
    divergence 𝕜 (fun xy : E×F => (f xy, g xy)) xy
    =
    divergence 𝕜 (fun x' => f (x',xy.2)) xy.1
    +
    divergence 𝕜 (fun y' => g (xy.1,y')) xy.2 := by
  obtain ⟨s, ⟨bX⟩⟩ := Basis.exists_basis 𝕜 E
  have : Fintype s := FiniteDimensional.fintypeBasisIndex bX
  obtain ⟨sY, ⟨bY⟩⟩ := Basis.exists_basis 𝕜 F
  have : Fintype sY := FiniteDimensional.fintypeBasisIndex bY
  let bXY := bX.prod bY
  rw[divergence_eq_sum_fderiv' bX]
  rw[divergence_eq_sum_fderiv' bY]
  rw[divergence_eq_sum_fderiv' bXY]
  simp[hf.fderiv_prodMk hg,bXY,fderiv_wrt_prod hf,fderiv_wrt_prod hg]
