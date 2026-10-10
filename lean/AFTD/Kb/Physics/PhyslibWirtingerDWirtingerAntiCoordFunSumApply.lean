import AFTD.Prelude
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoord
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirFunSum
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiDirNeg
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordConst
import AFTD.Kb.Physics.PhyslibWirtingerDWirtingerAntiCoordCoordProj

/-!
# Physlib.Wirtinger.dWirtingerAntiCoord_fun_sum_apply

Topic: classical_mechanics   Node: 8f7b72782a3a

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.dWirtingerAntiCoord_fun_sum_apply`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Pointwise finite-sum rule for anti-holomorphic coordinate derivatives at `u`: `∂̄_I (∑ a ∈ s, F a) = ∑ a ∈ s, ∂̄_I (F a)`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Physlib Physlib.Wirtinger in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
/-- Pointwise finite-sum rule for anti-holomorphic coordinate derivatives at `u`: `∂̄_I (∑ a ∈ s, F a) = ∑ a ∈ s, ∂̄_I (F a)`. -/
lemma Physlib.Wirtinger.dWirtingerAntiCoord_fun_sum_apply {α : Type*} {s : Finset α}
    {F : α → (ι → ℂ) → ℂ} {u : (ι → ℂ)}
    (hF : ∀ a ∈ s, DifferentiableAt ℝ (F a) u) (I : ι) :
    dWirtingerAntiCoord (fun v => ∑ a ∈ s, F a v) I u =
      ∑ a ∈ s, dWirtingerAntiCoord (F a) I u :=
  dWirtingerAntiDir_fun_sum hF (Pi.single I 1)
