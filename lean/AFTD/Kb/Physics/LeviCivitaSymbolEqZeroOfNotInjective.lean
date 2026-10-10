import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.LeviCivitaSymbolEqZeroOfEq
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.Physics.LeviCivitaSymbolPerm
import AFTD.Kb.GameTheoryEconomics.CatchUpBestMapNeLossIff

/-!
# leviCivitaSymbol_eq_zero_of_not_injective

Topic: classical_mechanics   Node: 93bd70b6b127

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_eq_zero_of_not_injective`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol vanishes on maps which are not injective.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol vanishes on maps which are not injective. -/
lemma leviCivitaSymbol_eq_zero_of_not_injective {g : ι → ι} (h : ¬ Function.Injective g) :
    leviCivitaSymbol g = 0 := by
  simp only [Function.Injective, not_forall] at h
  obtain ⟨i, j, hgij, hij⟩ := h
  exact leviCivitaSymbol_eq_zero_of_eq hij hgij
