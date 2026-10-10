import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirCongrOfEventuallyEq
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_congr_of_eventuallyEq_apply

Topic: classical_mechanics   Node: a54edc5d904d

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_congr_of_eventuallyEq_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`dWirtingerAntiCoord` is local (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂̄_I f₁ u = ∂̄_I f₂ u`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- `dWirtingerAntiCoord` is local (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂̄_I f₁ u = ∂̄_I f₂ u`). -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerAntiCoord f₁ I u = dWirtingerAntiCoord f₂ I u :=
  dWirtingerAntiDir_congr_of_eventuallyEq h (Pi.single I 1)
