import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSCat
import AFTD.Kb.Tcs.CslibLTSMorphism
import AFTD.Kb.Tcs.CslibLTSMorphismComp
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSWithIdle
import AFTD.Kb.Tcs.CslibLTSMorphismId

/-!
# Cslib.instCategoryLTSCat

Topic: computability   Node: 69016c59f5e2

Provenance: formalization of a published result. Source: CSLib, `Cslib.instCategoryLTSCat`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Finally, we prove that these form a category.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- Finally, we prove that these form a category. -/
instance Cslib.instCategoryLTSCat : CategoryTheory.Category LTSCat where
  Hom := LTS.Morphism
  id := LTS.Morphism.id
  comp := LTS.Morphism.comp
  comp_id _ := by
    simp only [LTS.Morphism.comp, LTS.Morphism.id]
    congr 1
    rw [fish_pure]
  assoc _ _ _ := by
    simp only [LTS.Morphism.comp]
    congr 1
    rw [fish_assoc]
