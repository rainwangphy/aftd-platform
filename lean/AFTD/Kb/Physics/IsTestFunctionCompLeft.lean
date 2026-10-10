import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction

/-!
# IsTestFunction.comp_left

Topic: classical_mechanics   Node: de6c65d24ecb

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.comp_left`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.comp_left
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
lemma IsTestFunction.comp_left {f : X → V'} (hf : IsTestFunction f)
    {g : V' → U} (hg1 : g 0 = 0) (hg : ContDiff ℝ ∞ g) :
    IsTestFunction (fun x => g (f x)) where
  smooth := ContDiff.comp hg hf.smooth
  supp := by
    obtain ⟨K, cK, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hf.supp
    refine exists_compact_iff_hasCompactSupport.mp ⟨K, cK, fun x hx => ?_⟩
    rw [hK x hx]
    exact hg1
