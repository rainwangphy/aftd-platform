import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDir
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirComp
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_comp_apply

Topic: classical_mechanics   Node: d850273aeaf0

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_comp_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The two-term coordinate chain rule for a real-differentiable outer `g`, anti-holomorphic version, pointwise at `u`: `∂̄_I (g ∘ f) = (∂g/∂f) · ∂̄_I f + (∂g/∂f̄) · ∂̄_I f̄`. Same outer coefficients as `dWirtingerCoord_comp_apply`, now multiplying the anti-holomorphic inner derivatives. The `d = Pi.single I 1` case of the foundation `dWirtingerAntiDir_comp`. The single-term holomorphic specialization `dWirtingerAntiCoord_comp_holomorphic_apply` is proved from this.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {g : ℂ → ℂ} {f : (ι → ℂ) → ℂ} in
/-- The two-term coordinate chain rule for a real-differentiable outer `g`, anti-holomorphic version, pointwise at `u`: `∂̄_I (g ∘ f) = (∂g/∂f) · ∂̄_I f + (∂g/∂f̄) · ∂̄_I f̄`. Same outer coefficients as `dWirtingerCoord_comp_apply`, now multiplying the anti-holomorphic inner derivatives. The `d = Pi.single I 1` case of the foundation `dWirtingerAntiDir_comp`. The single-term holomorphic specialization `dWirtingerAntiCoord_comp_holomorphic_apply` is proved from this. -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_comp_apply {u : (ι → ℂ)}
    (hg : DifferentiableAt ℝ g (f u)) (hf : DifferentiableAt ℝ f u) (I : ι) :
    dWirtingerAntiCoord (fun v => g (f v)) I u =
      dWirtingerDir g 1 (f u) * dWirtingerAntiCoord f I u
        + dWirtingerAntiDir g 1 (f u) *
          dWirtingerAntiCoord (fun v : (ι → ℂ) => star (f v)) I u :=
  dWirtingerAntiDir_comp hg hf (Pi.single I 1)
