import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.pi

Topic: classical_mechanics   Node: 2a588f9f817e

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.pi`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.pi
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Module in
variable
  {X} [NormedAddCommGroup X] [NormedSpace ℝ X]
  {U} [NormedAddCommGroup U] [NormedSpace ℝ U]
  {V'} [NormedAddCommGroup V'] [NormedSpace ℝ V'] in
open ContDiff InnerProductSpace MeasureTheory in
@[fun_prop]
lemma IsTestFunction.pi {ι} [Fintype ι] {φ : X → ι → U} (hφ : ∀ i, IsTestFunction (φ · i)) :
    IsTestFunction (fun x i => φ x i) where
  smooth := contDiff_pi' (fun i => (hφ i).smooth)
  supp := by
    let K : ι → Set X := fun i =>
      Classical.choose (exists_compact_iff_hasCompactSupport.mpr (hφ i).supp)
    have hK (i : ι) := Classical.choose_spec (exists_compact_iff_hasCompactSupport.mpr (hφ i).supp)
    refine exists_compact_iff_hasCompactSupport.mp
      ⟨⋃ i, K i, isCompact_iUnion (fun i => (hK i).1), fun x hx => ?_⟩
    simp at hx
    conv_lhs =>
      enter [i]
      rw [(hK i).2 x (hx i)]
    rfl
