import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.LeviCivitaSymbolPerm
import AFTD.Kb.Physics.LeviCivitaSymbolEqZeroOfNotInjective
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId

/-!
# leviCivitaSymbol_eq_zero_iff

Topic: classical_mechanics   Node: ee18296ecb0b

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_eq_zero_iff`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol vanishes exactly on maps with a repeated index, i.e. on maps which are not injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol vanishes exactly on maps with a repeated index, i.e. on maps which are not injective. -/
lemma leviCivitaSymbol_eq_zero_iff {g : ι → ι} :
    leviCivitaSymbol g = 0 ↔ ¬ Function.Injective g := by
  refine ⟨fun h hinj => ?_, leviCivitaSymbol_eq_zero_of_not_injective⟩
  obtain ⟨σ, rfl⟩ : ∃ σ : Equiv.Perm ι, ⇑σ = g :=
    ⟨Equiv.ofBijective g (Finite.injective_iff_bijective.mp hinj), rfl⟩
  rw [leviCivitaSymbol_perm] at h
  exact Units.ne_zero (Equiv.Perm.sign σ) h
