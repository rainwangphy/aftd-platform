import AFTD.Prelude
import AFTD.Kb.Tcs.CslibLTSCat
import AFTD.Kb.Tcs.CslibLTSMorphism
import AFTD.Kb.Tcs.CslibLTS
import AFTD.Kb.Tcs.CslibLTSWithIdle
import AFTD.Kb.Tcs.G

/-!
# Cslib.LTS.Morphism.comp

Topic: computability   Node: 5801bd8923d9

Provenance: formalization of a published result. Source: CSLib, `Cslib.LTS.Morphism.comp`. Lean proof by Ayberk Tosun, from https://github.com/leanprover/cslib/blob/3951377e5a3f5772737f11cd62bc5bb6a72f95d1/Cslib/Foundations/Semantics/LTS/LTSCat/Basic.lean (Copyright (c) 2026 Ayberk Tosun (Zeroth Research). All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Composition of LTS morphisms. We use Kleisli composition to define this.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {State Label : Type*} in
/-- Composition of LTS morphisms. We use Kleisli composition to define this. -/
def Cslib.LTS.Morphism.comp {lts₁ lts₂ lts₃} (f : LTS.Morphism lts₁ lts₂) (g : LTS.Morphism lts₂ lts₃) :
    LTS.Morphism lts₁ lts₃ where
  stateMap := g.stateMap ∘ f.stateMap
  labelMap := f.labelMap >=> g.labelMap
  labelMap_tr s s' l h := by
    obtain ⟨f, μ, p⟩ := f
    obtain ⟨g, ν, q⟩ := g
    simp only [LTS.withIdle] at p q
    change ((μ l).bind ν).elim (g (f s) = g (f s')) _
    cases hμ : μ l with grind
