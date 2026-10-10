import AFTD.Prelude
import AFTD.Kb.Physics.LeviCivitaSymbol
import AFTD.Kb.Physics.KroneckerDeltaKroneckerDelta
import AFTD.Kb.Physics.LeviCivitaSymbolEqDet
import AFTD.Kb.Physics.KroneckerDeltaGeneralizedKroneckerDeltaCompPerm
import AFTD.Kb.Physics.LeviCivitaSymbolId
import AFTD.Kb.Physics.LeviCivitaSymbolPerm

/-!
# leviCivitaSymbol_eq_zero_of_eq

Topic: classical_mechanics   Node: 6bddbc709505

Provenance: formalization of a published result. Source: Physlib, `leviCivitaSymbol_eq_zero_of_eq`. Lean proof by Robert Sneiderman, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/LeviCivita/Basic.lean (Copyright (c) 2026 Robert Sneiderman. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The Levi-Civita symbol vanishes on a repeated index: if two distinct index positions `i ≠ j` carry the same value, the symbol is zero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open KroneckerDelta in
variable {ι : Type} [DecidableEq ι] [Fintype ι] in
/-- The Levi-Civita symbol vanishes on a repeated index: if two distinct index positions `i ≠ j` carry the same value, the symbol is zero. -/
lemma leviCivitaSymbol_eq_zero_of_eq {g : ι → ι} {i j : ι} (hij : i ≠ j) (h : g i = g j) :
    leviCivitaSymbol g = 0 := by
  rw [leviCivitaSymbol_eq_det]
  exact Matrix.det_zero_of_row_eq hij (funext fun c => by rw [h])
