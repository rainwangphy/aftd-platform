import AFTD.Prelude
import AFTD.Kb.Physics.IsTestFunction
import AFTD.Kb.Physics.IsTestFunctionContDiff

/-!
# IsTestFunction.prodMk

Topic: classical_mechanics   Node: 4e47370a8bb1

Provenance: formalization of a published result. Source: Physlib, `IsTestFunction.prodMk`. Lean proof by Tomas Skrivan, Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/VariationalCalculus/IsTestFunction.lean (Copyright (c) 2025 Tomas Skrivan. All rights reserved, Apache-2.0); 1 adapted; compiled here.

IsTestFunction.prodMk
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
lemma IsTestFunction.prodMk {f : X → U} {g : X → V'}
    (hf : IsTestFunction f) (hg : IsTestFunction g) :
    IsTestFunction (fun x => (f x, g x)) where
  smooth := by fun_prop
  supp := by
    obtain ⟨Kf, cKf, hKf⟩ := exists_compact_iff_hasCompactSupport.mpr hf.supp
    obtain ⟨Kg, cKg, hKg⟩ := exists_compact_iff_hasCompactSupport.mpr hg.supp
    refine exists_compact_iff_hasCompactSupport.mp
      ⟨Kf ∪ Kg, IsCompact.union cKf cKg, fun x hx => ?_⟩
    simp at hx
    simp [hKf x hx.1, hKg x hx.2]
