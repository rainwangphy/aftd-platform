import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirCongrOfEventuallyEq
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg

/-!
# Physlib.Wirtinger.dWirtingerCoord_congr_of_eventuallyEq_apply

Topic: classical_mechanics   Node: e883a96c9a8a

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerCoord_congr_of_eventuallyEq_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

`dWirtingerCoord` is local: functions agreeing on a neighbourhood of `u` have equal holomorphic Wirtinger derivative at `u` (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂_I f₁ u = ∂_I f₂ u`).
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- `dWirtingerCoord` is local: functions agreeing on a neighbourhood of `u` have equal holomorphic Wirtinger derivative at `u` (`f₁ =ᶠ[nhds u] f₂ ⟹ ∂_I f₁ u = ∂_I f₂ u`). -/
lemma Physlib.Wirtinger.dWirtingerCoord_congr_of_eventuallyEq_apply {f₁ f₂ : (ι → ℂ) → ℂ}
    {u : (ι → ℂ)} (h : f₁ =ᶠ[nhds u] f₂) (I : ι) :
    dWirtingerCoord f₁ I u = dWirtingerCoord f₂ I u :=
  dWirtingerDir_congr_of_eventuallyEq h (Pi.single I 1)
